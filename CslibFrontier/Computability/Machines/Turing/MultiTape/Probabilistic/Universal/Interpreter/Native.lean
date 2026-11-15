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
* `Turing.MultiTapePTM.Universal.NativeInterpreter.RetainedCommandInput`: narrow stored-state and
  selected-command boundary for retained query branches.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.RetainedQueryPayload` and
  `retainedCommandQueryPayloadCompiler`: shared selected-query view and compiler boundary.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.bodyWithQueryBranch`: shared retained
  coin/lookup/command/controller construction for a supplied stateful query artifact.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.body`: retained one-round interpreter.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.artifact`: retained complete interpreter.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.generatedStaticBits`: exact generated artifact
  size, separate from runtime input, supplied description and emitted output sizes.

## Main results

* `Turing.MultiTapePTM.Universal.NativeInterpreter.bodyProgramWithQueryBranch_active`: exact
  fair-coin, lookup and local-or-query semantics of the generic active branch.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.machine_bodyWithQueryBranch_succ` and
  `Turing.MultiTapePTM.Universal.NativeInterpreter.online_bodyWithQueryBranch_succ`: exact
  retained-machine and phase-accounting decompositions of the nonempty-channel constructor.
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

/-- Two retained states agree on every field that one interpreter round must preserve. -/
structure LoopState.SameStatic (first second : LoopState) : Prop where
  /-- The source description is unchanged. -/
  desc : second.desc = first.desc
  /-- The source input is unchanged. -/
  input : second.input = first.input
  /-- The source fuel bound is unchanged. -/
  fuel : second.fuel = first.fuel
  /-- The raw reply-copy bound is unchanged. -/
  replyBits : second.replyBits = first.replyBits

/-- Constructive proof decoder used only by the typed bounded-iteration theorem. The retained body
still executes and charges its concrete parsers. -/
def loopStateDecoder : Decoder eLoopState :=
  (Decoder.pair descDecoder
    (.pair (.list .unary)
      (.pair .unary (.pair .unary (.pair .unary iCfgDecoder))))).map
    (fun ⟨desc, input, fuel, replyBits, remaining, cfg⟩ =>
      ⟨desc, input, fuel, replyBits, remaining, cfg⟩)
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
private abbrev eRunTail : RunTail ↪ List Bool := eRunParameters

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

private abbrev StoredInput (S : Type) := Option S
private def eStoredInput (encState : S ↪ List Bool) : StoredInput S ↪ List Bool :=
  encOption encState
private abbrev StoredCoinInput (S : Type) := StoredInput S × Bool
private def eStoredCoinInput (encState : S ↪ List Bool) : StoredCoinInput S ↪ List Bool :=
  encPair (eStoredInput encState) encBool
private abbrev StoredLookupInput (S : Type) := StoredCoinInput S × Option Branches
private def eStoredLookupInput (encState : S ↪ List Bool) :
    StoredLookupInput S ↪ List Bool :=
  encPair (eStoredCoinInput encState) (encOption eBranches)

private abbrev BodyInput := StoredInput LoopState
private def eBodyInput : BodyInput ↪ List Bool := eStoredInput eLoopState
private abbrev CoinInput := StoredCoinInput LoopState
private def eCoinInput : CoinInput ↪ List Bool := eStoredCoinInput eLoopState
private abbrev LookupInput := StoredLookupInput LoopState
private def eLookupInput : LookupInput ↪ List Bool := eStoredLookupInput eLoopState

private noncomputable def storedStateCompiler [Inhabited S]
    (encState : S ↪ List Bool) :
    NativeCompiler (fun state : StoredInput S => state.getD default)
      (eStoredInput encState) encState :=
  NativeCompiler.optionGetD default encState

private noncomputable def storedSourceCompiler [Inhabited S]
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState) :
    NativeCompiler (fun state : StoredInput S => source (state.getD default))
      (eStoredInput encState) eLoopState :=
  sourceCompiler.comp (storedStateCompiler encState)

private noncomputable def storedCfgCompiler [Inhabited S]
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState) :
    NativeCompiler (fun state : StoredInput S => (source (state.getD default)).cfg)
      (eStoredInput encState) eICfg :=
  cfgCompiler.comp (storedSourceCompiler encState source sourceCompiler)

private noncomputable def storedRemainingCompiler [Inhabited S]
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState) :
    NativeCompiler (fun state : StoredInput S => (source (state.getD default)).remaining)
      (eStoredInput encState) encUnary :=
  remainingCompiler.comp (storedSourceCompiler encState source sourceCompiler)

private noncomputable def advanceStoredCompiler [Inhabited S]
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState) :
    NativeCompiler (fun state : StoredInput S =>
      some (update (state.getD default, (source (state.getD default)).cfg)))
      (eStoredInput encState) (eStoredInput encState) :=
  (NativeCompiler.optionSome encState).comp
    (updateCompiler.comp ((storedStateCompiler encState).pair
      (storedCfgCompiler encState source sourceCompiler)))

private noncomputable def bodyStateCompiler :
    NativeCompiler (fun state : BodyInput => state.getD default) eBodyInput eLoopState :=
  storedStateCompiler eLoopState

private abbrev CommandAtInput := Desc × (List ℕ × (ICfg × Bool))
private def eCommandAtInput : CommandAtInput ↪ List Bool :=
  encPair eDesc (encPair (encList encUnary) (encPair eICfg encBool))
private abbrev CommandAtLookupInput := CommandAtInput × Option Branches
private def eCommandAtLookupInput : CommandAtLookupInput ↪ List Bool :=
  encPair eCommandAtInput (encOption eBranches)

private def toStoredCommandAtInput [Inhabited S] (source : S → LoopState)
    (input : StoredCoinInput S) : CommandAtInput :=
  let state := source (input.1.getD default)
  (state.desc, state.input, state.cfg, input.2)

private def toCommandAtInput (input : CoinInput) : CommandAtInput :=
  toStoredCommandAtInput id input

private noncomputable def storedCommandAtInputCompiler [Inhabited S]
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState) :
    NativeCompiler (toStoredCommandAtInput source)
      (eStoredCoinInput encState) eCommandAtInput := by
  let state := (storedSourceCompiler encState source sourceCompiler).comp
    (NativeCompiler.first (eStoredInput encState) encBool)
  let coin := NativeCompiler.second (eStoredInput encState) encBool
  let fields := (descCompiler.comp state).pair
    ((inputCompiler.comp state).pair ((cfgCompiler.comp state).pair coin))
  exact fields.ofOutputEq fun _ => rfl

private noncomputable def storedCommandAtLookupInputCompiler [Inhabited S]
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState) :
    NativeCompiler
      (fun input : StoredLookupInput S =>
        (toStoredCommandAtInput source input.1, input.2))
      (eStoredLookupInput encState) eCommandAtLookupInput := by
  let coinInput := NativeCompiler.first (eStoredCoinInput encState) (encOption eBranches)
  let lookup := NativeCompiler.second (eStoredCoinInput encState) (encOption eBranches)
  exact ((storedCommandAtInputCompiler encState source sourceCompiler).comp coinInput).pair lookup

private noncomputable def storedCommandCompiler [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState) :
    NativeCompiler
      (fun input : StoredLookupInput S =>
        commandAtFromLookup r (toStoredCommandAtInput source input.1, input.2))
      (eStoredLookupInput encState) (eCommand r) :=
  (ICfg.commandAtFromLookupCompiler r).comp
    (storedCommandAtLookupInputCompiler encState source sourceCompiler)

/-- Retained post-lookup command interpreter. The table scan itself is deliberately outside this
compiler so it can be charged once in the `lookup` phase. -/
noncomputable def commandCompiler (r : ℕ) :
    NativeCompiler
      (fun input : LookupInput =>
        commandAtFromLookup r (toCommandAtInput input.1, input.2))
      eLookupInput (eCommand r) :=
  storedCommandCompiler r eLoopState id (NativeCompiler.identity eLoopState)

/-- Operation, source request, continuation tag and suspended configuration selected from a
retained command. This is the shared typed view used by both the open query executor and locally
installed handlers. -/
structure RetainedQueryPayload (r : ℕ) where
  /-- Selected source operation. -/
  operation : Fin r
  /-- Decoded source request symbols. -/
  request : List ℕ
  /-- Continuation control tag. -/
  next : ℕ
  /-- Suspended source configuration awaiting the reply. -/
  pending : ICfg

/-- Field-order encoding of the retained-query view: operation, request, continuation tag and
suspended configuration. Every field except the last is framed. -/
enc_structure eRetainedQueryPayload (r : ℕ) : RetainedQueryPayload r where
  operation : (eOperation r), request : (encList encUnary), next : encUnary, pending : eICfg

private abbrev CommandSum (r : ℕ) := ICfg ⊕ RetainedQueryPayload r
private def eCommandSum (r : ℕ) : CommandSum r ↪ List Bool :=
  encSum eICfg (eRetainedQueryPayload r)

/-- The narrow retained-command boundary: stored controller state and the selected command. -/
abbrev RetainedCommandInput (r : ℕ) (S : Type) := S × Command r

/-- Encoding of stored state followed by the selected command. -/
def eRetainedCommandInput (r : ℕ) (encState : S ↪ List Bool) :
    RetainedCommandInput r S ↪ List Bool :=
  encPair encState (eCommand r)

private abbrev CommandInput (r : ℕ) := RetainedCommandInput r LoopState
private def eCommandInput (r : ℕ) : CommandInput r ↪ List Bool :=
  eRetainedCommandInput r eLoopState

/-- Total fallback for viewing a local command through the retained-query boundary. The fallback
is used only on the local branch, before the command tag dispatch excludes that branch. -/
private def defaultRetainedQueryPayload {r : ℕ} (fallback : Fin r) : RetainedQueryPayload r :=
  { operation := fallback, request := [], next := 0, pending := default }

private def commandSumView (r : ℕ) : Command r → CommandSum r
  | .local cfg => .inl cfg
  | .query operation request next pending =>
      .inr { operation, request, next, pending }

/-- Total shared retained-query view of a selected command. -/
def retainedCommandQueryPayload (r : ℕ) (fallback : Fin r)
    (input : RetainedCommandInput r S) : RetainedQueryPayload r :=
  Sum.elim (Function.const ICfg (defaultRetainedQueryPayload fallback)) id
    (commandSumView r input.2)

private def commandState (input : CommandInput r) : LoopState :=
  input.1

private noncomputable def commandSumCompiler (r : ℕ) :
    NativeCompiler (commandSumView r) (eCommand r) (eCommandSum r) :=
  (NativeCompiler.identity (eCommandSum r)).ofInputEq (commandSumView r) fun command => by
    cases command <;> rfl

private noncomputable def retainedCommandValueCompiler (r : ℕ)
    (encState : S ↪ List Bool) :
    NativeCompiler (fun input : RetainedCommandInput r S => input.2)
      (eRetainedCommandInput r encState) (eCommand r) :=
  NativeCompiler.second encState (eCommand r)

private noncomputable def retainedCommandSumInputCompiler (r : ℕ)
    (encState : S ↪ List Bool) :
    NativeCompiler (fun input : RetainedCommandInput r S => commandSumView r input.2)
      (eRetainedCommandInput r encState) (eCommandSum r) :=
  (commandSumCompiler r).comp (retainedCommandValueCompiler r encState)

private noncomputable def retainedCommandIsQueryCompiler (r : ℕ)
    (encState : S ↪ List Bool) :
    NativeCompiler
      (fun input : RetainedCommandInput r S => (commandSumView r input.2).isRight)
      (eRetainedCommandInput r encState) encTest :=
  NativeCompiler.boolToTest.comp
    ((NativeCompiler.sumTag eICfg (eRetainedQueryPayload r)).comp
      (retainedCommandSumInputCompiler r encState))

private noncomputable def retainedLocalCfgCompiler (r : ℕ)
    (encState : S ↪ List Bool) :
    NativeCompiler
      (fun input : RetainedCommandInput r S =>
        Sum.elim id (Function.const (RetainedQueryPayload r) default)
          (commandSumView r input.2))
      (eRetainedCommandInput r encState) eICfg :=
  (NativeCompiler.sumLeftD default eICfg (eRetainedQueryPayload r)).comp
    (retainedCommandSumInputCompiler r encState)

/-- Compiler for the shared retained-query view. Consumers can project its four fields without
rebuilding the command-sum decoding chain. -/
noncomputable def retainedCommandQueryPayloadCompiler (r : ℕ) (fallback : Fin r)
    (encState : S ↪ List Bool) :
    NativeCompiler
      (retainedCommandQueryPayload r fallback : RetainedCommandInput r S → _)
      (eRetainedCommandInput r encState) (eRetainedQueryPayload r) :=
  (NativeCompiler.sumRightD (defaultRetainedQueryPayload fallback) eICfg
    (eRetainedQueryPayload r)).comp (retainedCommandSumInputCompiler r encState)

private noncomputable def commandLoopStateCompiler (r : ℕ) :
    NativeCompiler (commandState : CommandInput r → LoopState)
      (eCommandInput r) eLoopState :=
  NativeCompiler.first eLoopState (eCommand r)

private noncomputable def retainedLocalAdvanceCompiler (r : ℕ)
    (encState : S ↪ List Bool) (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState) :
    NativeCompiler (fun input : RetainedCommandInput r S =>
      some (update (input.1,
        Sum.elim id (Function.const (RetainedQueryPayload r) default)
          (commandSumView r input.2))))
      (eRetainedCommandInput r encState) (eStoredInput encState) :=
  (NativeCompiler.optionSome encState).comp
    (updateCompiler.comp
      ((NativeCompiler.first encState (eCommand r)).pair
        (retainedLocalCfgCompiler r encState)))

private noncomputable def localAdvanceCompiler (r : ℕ) :
    NativeCompiler (fun input : CommandInput r =>
      some (input.1.advance
        (Sum.elim id (Function.const (RetainedQueryPayload r) default)
          (commandSumView r input.2))))
      (eCommandInput r) eBodyInput :=
  retainedLocalAdvanceCompiler r eLoopState (fun input => input.1.advance input.2)
    advanceCompiler

private noncomputable def queryPayloadFieldsCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r =>
        let payload := retainedCommandQueryPayload r fallback input
        (payload.operation, payload.request, payload.next, payload.pending))
      (eCommandInput r)
      (encPair (eOperation r) (encPair (encList encUnary) (encPair encUnary eICfg))) :=
  let fields := fun payload : RetainedQueryPayload r =>
    (payload.operation, payload.request, payload.next, payload.pending)
  ((NativeCompiler.identity
      (encPair (eOperation r) (encPair (encList encUnary) (encPair encUnary eICfg))))
    |>.ofInputEq fields fun _ => rfl).comp
      (retainedCommandQueryPayloadCompiler r fallback eLoopState)

private noncomputable def queryOperationCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r => (retainedCommandQueryPayload r fallback input).operation)
      (eCommandInput r) (eOperation r) :=
  (NativeCompiler.first (eOperation r)
    (encPair (encList encUnary) (encPair encUnary eICfg))).comp
      (queryPayloadFieldsCompiler r fallback)

private noncomputable def queryTailCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r =>
        ((retainedCommandQueryPayload r fallback input).request,
          (retainedCommandQueryPayload r fallback input).next,
          (retainedCommandQueryPayload r fallback input).pending))
      (eCommandInput r) (encPair (encList encUnary) (encPair encUnary eICfg)) :=
  (NativeCompiler.second (eOperation r)
    (encPair (encList encUnary) (encPair encUnary eICfg))).comp
      (queryPayloadFieldsCompiler r fallback)

private noncomputable def queryRequestCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r => (retainedCommandQueryPayload r fallback input).request)
      (eCommandInput r) (encList encUnary) :=
  (NativeCompiler.first (encList encUnary) (encPair encUnary eICfg)).comp
    (queryTailCompiler r fallback)

private noncomputable def queryNextCfgCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r =>
        ((retainedCommandQueryPayload r fallback input).next,
          (retainedCommandQueryPayload r fallback input).pending))
      (eCommandInput r) (encPair encUnary eICfg) :=
  (NativeCompiler.second (encList encUnary) (encPair encUnary eICfg)).comp
    (queryTailCompiler r fallback)

private noncomputable def queryNextCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r => (retainedCommandQueryPayload r fallback input).next)
      (eCommandInput r) encUnary :=
  (NativeCompiler.first encUnary eICfg).comp (queryNextCfgCompiler r fallback)

private noncomputable def queryCfgCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r => (retainedCommandQueryPayload r fallback input).pending)
      (eCommandInput r) eICfg :=
  (NativeCompiler.second encUnary eICfg).comp (queryNextCfgCompiler r fallback)

private noncomputable def queryRequestWordCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r =>
        encList encUnary (retainedCommandQueryPayload r fallback input).request)
      (eCommandInput r) encBits :=
  (queryRequestCompiler r fallback).ofOutputEq fun _ => rfl

private noncomputable def queryReplyBitsCompiler (r : ℕ) :
    NativeCompiler
      (fun input : CommandInput r => (commandState input).replyBits)
      (eCommandInput r) encUnary :=
  replyBitsCompiler.comp (commandLoopStateCompiler r)

private def queryInput (r : ℕ) (fallback : Fin r) (input : CommandInput r) :
    List Bool × ℕ :=
  (encList encUnary (retainedCommandQueryPayload r fallback input).request,
    (commandState input).replyBits)

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
  let state := commandState command
  let payload := retainedCommandQueryPayload r fallback command
  let decoded := (frames input.2).map List.length |>.take state.fuel
  some (state.advance payload.pending.receive payload.operation payload.next decoded)

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

private theorem machine_castProgram {r : ℕ} {Alpha Beta : Type}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    {first second : Alpha → WordOracleComp (Fin r) Beta}
    (witness : NativeOracleProgram r first encIn encOut) (h : first = second) :
    (castProgram witness h).machine = witness.machine := by
  subst second
  rfl

private theorem online_castProgram {r : ℕ} {Alpha Beta : Type}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    {first second : Alpha → WordOracleComp (Fin r) Beta}
    (witness : NativeOracleProgram r first encIn encOut) (h : first = second) :
    (castProgram witness h).online = witness.online := by
  subst second
  rfl

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
  (BitString.shortWords (commandState input).replyBits).toList

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
    (hreply : reply.length ≤ (commandState input).replyBits) (phase : OnlinePhase) :
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
  encTest (decide ((retainedCommandQueryPayload r fallback input).operation = operation))

private noncomputable def operationNatCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r =>
        (retainedCommandQueryPayload r fallback input).operation.val)
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
  some ((commandState input).advance
    (Sum.elim id (Function.const (RetainedQueryPayload r) default)
      (commandSumView r input.2)))

noncomputable def queryFallback (r : ℕ) :=
  NativeOracleProgram.ofCompiler (r := r)
    (ClassifiedCompiler.inPhase .controller (localAdvanceCompiler r))

/-- Actual finite fixed-operation dispatcher. For `r = 0` the case list is empty. -/
noncomputable def queryDispatch (r : ℕ) (fallback : Fin r) :=
  NativeOracleProgram.finiteDispatch
    ((operations r).map (operationCase r fallback)) (queryFallback r)

private def executeRetainedCommand (r : ℕ) (update : S × ICfg → S)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (input : RetainedCommandInput r S) : WordOracleComp (Fin external) (Option S) :=
  match input.2 with
  | .local cfg => pure (some (update (input.1, cfg)))
  | .query _ _ _ _ => queryProgram input

private noncomputable def retainedLocalArtifact (external r : ℕ)
    (encState : S ↪ List Bool) (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState) :=
  NativeOracleProgram.ofCompiler (r := external)
    (ClassifiedCompiler.inPhase .controller
      (retainedLocalAdvanceCompiler r encState update updateCompiler))

/-- Reusable command executor with a supplied retained query branch. Local commands use the
provided state update compiler; query commands run the supplied artifact on only stored state and
the selected command. -/
private noncomputable def commandExecutorWithQueryBranch (r : ℕ)
    (encState : S ↪ List Bool) (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    {queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (queryArtifact : NativeOracleProgram external queryProgram
      (eRetainedCommandInput r encState) (encOption encState)) :
    NativeOracleProgram external (executeRetainedCommand r update queryProgram)
      (eRetainedCommandInput r encState) (encOption encState) := by
  let condition := ClassifiedCompiler.inPhase .tags
    (retainedCommandIsQueryCompiler r encState)
  let assembled := NativeOracleProgram.dispatch condition queryArtifact
    (retainedLocalArtifact external r encState update updateCompiler)
  apply castProgram assembled
  funext input
  cases input.2 <;>
    simp [executeRetainedCommand, NativeOracleProgram.dispatchProgram,
      retainedCommandIsQueryCompiler, retainedCommandSumInputCompiler,
      retainedCommandValueCompiler, commandSumCompiler, commandSumView]

private noncomputable def commandExecutorZeroWithQueryProgram
    (encState : S ↪ List Bool) (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    (queryProgram : RetainedCommandInput 0 S → WordOracleComp (Fin external) (Option S)) :
    NativeOracleProgram external (executeRetainedCommand 0 update queryProgram)
      (eRetainedCommandInput 0 encState) (encOption encState) := by
  let local := retainedLocalArtifact external 0 encState update updateCompiler
  apply castProgram local
  funext input
  cases input.2 with
  | local cfg => rfl
  | query operation request next cfg => exact Fin.elim0 operation

private theorem dispatchProgram_operations (r : ℕ) (fallback operation : Fin r)
    (input : CommandInput r)
    (hoperation : (retainedCommandQueryPayload r fallback input).operation = operation) :
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
        simp [operationCase, operationTest, hoperation]
      · have hne : operation ≠ head := fun hop => h hop.symm
        have htail : operation ∈ tail := (List.mem_cons.mp hmem).resolve_left hne
        simp only [operationCase, operationTest, hoperation, hne, decide_false, encTest_apply,
          Bool.false_eq_true, List.replicate_zero]
        exact ih htail

private def originalQueryProgram : (r : ℕ) →
    RetainedCommandInput r LoopState → WordOracleComp (Fin r) BodyInput
  | 0, input => pure (localAdvance 0 input)
  | r + 1, input =>
      NativeOracleProgram.dispatchProgram
        ((operations (r + 1)).map (operationCase (r + 1) 0))
        (fun command => pure (localAdvance (r + 1) command)) input

private noncomputable def originalQueryArtifact : (r : ℕ) →
    NativeOracleProgram r (originalQueryProgram r) (eCommandInput r) eBodyInput
  | 0 => queryFallback 0
  | r + 1 => queryDispatch (r + 1) 0

private def executeCommand (r : ℕ) (fallback : Fin r)
    (input : CommandInput r) : WordOracleComp (Fin r) BodyInput :=
  match input.2 with
  | .local cfg => pure (some ((commandState input).advance cfg))
  | .query operation _ _ _ => queryBranchProgram r fallback operation input

private def commandProgram : (r : ℕ) → CommandInput r → WordOracleComp (Fin r) BodyInput
  | 0, input =>
      match input.2 with
      | .local cfg => pure (some ((commandState input).advance cfg))
      | .query operation _ _ _ => Fin.elim0 operation
  | r + 1, input => executeCommand (r + 1) 0 input

/-- Complete validated-command executor for a nonempty fixed channel type. The command tag is
tested by a retained compiler, and query selection is a literal finite dispatcher. -/
noncomputable def commandExecutorSucc (r : ℕ) :
    NativeOracleProgram (r + 1) (executeCommand (r + 1) 0)
      (eCommandInput (r + 1)) eBodyInput := by
  let assembled := commandExecutorWithQueryBranch (r + 1) eLoopState
    (fun input => input.1.advance input.2) advanceCompiler (originalQueryArtifact (r + 1))
  apply castProgram assembled
  funext input
  cases input.2 with
  | local cfg => rfl
  | query operation request next cfg =>
      simp only [executeCommand, executeRetainedCommand]
      exact dispatchProgram_operations (r + 1) 0 operation input rfl

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

private def storedLookupResult [Inhabited S] (source : S → LoopState)
    (input : StoredCoinInput S) : Option Branches :=
  let commandInput := toStoredCommandAtInput source input
  NativeCompiler.firstMatch (commandInput.1.table,
    commandInput.2.2.1.key commandInput.2.1
      ((commandInput.2.2.1.control.getD none).getD 0))

private def lookupResult (input : CoinInput) : Option Branches :=
  storedLookupResult id input

private noncomputable def storedLookupArtifact [Inhabited S] (external r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState) :
    NativeOracleProgram external
      (fun input : StoredCoinInput S => pure (storedLookupResult source input))
      (eStoredCoinInput encState) (encOption eBranches) :=
  NativeOracleProgram.preprocess
    (ClassifiedCompiler.inPhase .marshalling
      (storedCommandAtInputCompiler encState source sourceCompiler))
    (NativeOracleProgram.ofCompiler (r := external)
      (ClassifiedCompiler.inPhase .lookup ICfg.commandAtLookupCompiler))

/-- The lookup scan is an actual retained deterministic artifact, after explicit marshalling of
the active loop state and private coin. -/
noncomputable def lookupArtifact (r : ℕ) :
    NativeOracleProgram r (fun input : CoinInput => pure (lookupResult input))
      eCoinInput (encOption eBranches) :=
  storedLookupArtifact r r eLoopState id (NativeCompiler.identity eLoopState)

private def commandFromStoredLookup [Inhabited S] (r : ℕ) (source : S → LoopState)
    (input : StoredLookupInput S) : Command r :=
  commandAtFromLookup r (toStoredCommandAtInput source input.1, input.2)

private def commandFromLookup (r : ℕ) (input : LookupInput) : Command r :=
  commandFromStoredLookup r id input

private noncomputable def commandFromStoredLookupArtifact [Inhabited S] (external r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState) :
    NativeOracleProgram external
      (fun input : StoredLookupInput S => pure (commandFromStoredLookup r source input))
      (eStoredLookupInput encState) (eCommand r) :=
  NativeOracleProgram.ofCompiler (r := external)
    (ClassifiedCompiler.inPhase .localStep
      (storedCommandCompiler r encState source sourceCompiler))

/-- Retained post-lookup command construction. It performs no table scan. -/
noncomputable def commandFromLookupArtifact (r : ℕ) :
    NativeOracleProgram r (fun input : LookupInput => pure (commandFromLookup r input))
      eLookupInput (eCommand r) :=
  commandFromStoredLookupArtifact r r eLoopState id (NativeCompiler.identity eLoopState)

private def retainedCommandFromLookup [Inhabited S] (r : ℕ)
    (input : StoredLookupInput S × Command r) : RetainedCommandInput r S :=
  (input.1.1.1.getD default, input.2)

private noncomputable def retainedCommandFromLookupCompiler [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) :
    NativeCompiler (retainedCommandFromLookup r)
      (encPair (eStoredLookupInput encState) (eCommand r))
      (eRetainedCommandInput r encState) := by
  let lookup := NativeCompiler.first (eStoredLookupInput encState) (eCommand r)
  let coin := (NativeCompiler.first (eStoredCoinInput encState) (encOption eBranches)).comp lookup
  let stored := (NativeCompiler.first (eStoredInput encState) encBool).comp coin
  let state := (storedStateCompiler encState).comp stored
  let command := NativeCompiler.second (eStoredLookupInput encState) (eCommand r)
  exact state.pair command

private noncomputable def preparedCommandArtifact [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState)) :=
  NativeOracleProgram.preprocess
    (ClassifiedCompiler.inPhase .marshalling
      (retainedCommandFromLookupCompiler r encState)) commandArtifact

private def storedCommandExecutorOnline [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState)) :
    OnlineAccounting (StoredLookupInput S) :=
  (preparedCommandArtifact r encState commandArtifact).online.reindex fun input =>
    (input, commandFromStoredLookup r source input)

/-- Uniform resource record for the command executor at the unique deterministic command produced
from one captured lookup result. -/
def commandExecutorOnline (r : ℕ) : OnlineAccounting LookupInput :=
  storedCommandExecutorOnline r eLoopState id (commandExecutor r)

private theorem storedCommandExecutor_resource_bound [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState))
    (input : StoredLookupInput S) (OracleState : Type)
    (oracle : Fin external × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (command : Command r) (state' : OracleState)
    (hcommand : (command, state') ∈
      (ProbOracleComp.runWith oracle
        (pure (commandFromStoredLookup r source input)) state).support)
    (phase : OnlinePhase) :
    (preparedCommandArtifact r encState commandArtifact).online.time phase (input, command) ≤
        (storedCommandExecutorOnline r encState source commandArtifact).time phase input ∧
      (preparedCommandArtifact r encState commandArtifact).online.workspace phase
          (input, command) ≤
        (storedCommandExecutorOnline r encState source commandArtifact).workspace phase input := by
  simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hcommand
  rcases hcommand with ⟨rfl, rfl⟩
  exact ⟨le_rfl, le_rfl⟩

private theorem commandExecutor_resource_bound (r : ℕ) (input : LookupInput)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (command : Command r) (state' : OracleState)
    (hcommand : (command, state') ∈
      (ProbOracleComp.runWith oracle (pure (commandFromLookup r input)) state).support)
    (phase : OnlinePhase) :
    (preparedCommandArtifact r eLoopState (commandExecutor r)).online.time
        phase (input, command) ≤
        (commandExecutorOnline r).time phase input ∧
      (preparedCommandArtifact r eLoopState (commandExecutor r)).online.workspace
          phase (input, command) ≤
        (commandExecutorOnline r).workspace phase input := by
  exact storedCommandExecutor_resource_bound r eLoopState id
    (commandExecutor r) input OracleState oracle state command state' hcommand phase

private noncomputable def fromStoredLookupArtifact [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState)) :=
  NativeOracleProgram.sequenceCaptured
    (commandFromStoredLookupArtifact external r encState source sourceCompiler)
    (preparedCommandArtifact r encState commandArtifact)
    (storedCommandExecutorOnline r encState source commandArtifact)
    (storedCommandExecutor_resource_bound r encState source commandArtifact)

/-- Execute the captured post-lookup command, including any validated external query. -/
noncomputable def fromLookupArtifact (r : ℕ) :=
  fromStoredLookupArtifact r eLoopState id (NativeCompiler.identity eLoopState)
    (commandExecutor r)

private def storedFromLookupOnline [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState)) :
    OnlineAccounting (StoredCoinInput S) :=
  (fromStoredLookupArtifact r encState source sourceCompiler commandArtifact).online.reindex
    fun input => (input, storedLookupResult source input)

/-- Resource record for the unique deterministic table result on one coin-bearing input. -/
def fromLookupOnline (r : ℕ) : OnlineAccounting CoinInput :=
  storedFromLookupOnline r eLoopState id (NativeCompiler.identity eLoopState)
    (commandExecutor r)

private theorem storedFromLookup_resource_bound [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState))
    (input : StoredCoinInput S) (OracleState : Type)
    (oracle : Fin external × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (lookup : Option Branches) (state' : OracleState)
    (hlookup : (lookup, state') ∈
      (ProbOracleComp.runWith oracle (pure (storedLookupResult source input)) state).support)
    (phase : OnlinePhase) :
    (fromStoredLookupArtifact r encState source sourceCompiler commandArtifact).online.time phase
          (input, lookup) ≤
        (storedFromLookupOnline r encState source sourceCompiler commandArtifact).time phase
          input ∧
      (fromStoredLookupArtifact r encState source sourceCompiler
          commandArtifact).online.workspace phase (input, lookup) ≤
        (storedFromLookupOnline r encState source sourceCompiler
          commandArtifact).workspace phase input := by
  simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hlookup
  rcases hlookup with ⟨rfl, rfl⟩
  exact ⟨le_rfl, le_rfl⟩

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
  exact storedFromLookup_resource_bound r eLoopState id
    (NativeCompiler.identity eLoopState) (commandExecutor r) input OracleState oracle state
      lookup state' hlookup phase

private noncomputable def storedCoinRoundArtifact [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState)) :=
  NativeOracleProgram.sequenceCaptured
    (storedLookupArtifact external r encState source sourceCompiler)
    (fromStoredLookupArtifact r encState source sourceCompiler commandArtifact)
    (storedFromLookupOnline r encState source sourceCompiler commandArtifact)
    (storedFromLookup_resource_bound r encState source sourceCompiler commandArtifact)

/-- One coin-bearing active round with exactly one captured table scan. -/
noncomputable def coinRoundArtifact (r : ℕ) :=
  storedCoinRoundArtifact r eLoopState id (NativeCompiler.identity eLoopState)
    (commandExecutor r)

private def storedCoinRoundOnline [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState)) :
    OnlineAccounting (StoredInput S) where
  time := fun phase input =>
    max (storedCoinRoundArtifact r encState source sourceCompiler
        commandArtifact).online.time phase (input, false)
      ((storedCoinRoundArtifact r encState source sourceCompiler
        commandArtifact).online.time phase (input, true))
  workspace := fun phase input =>
    max (storedCoinRoundArtifact r encState source sourceCompiler
        commandArtifact).online.workspace phase (input, false)
      ((storedCoinRoundArtifact r encState source sourceCompiler
        commandArtifact).online.workspace phase (input, true))

/-- Phasewise maximum of the active continuation over the two fair-coin outcomes. -/
def coinRoundOnline (r : ℕ) : OnlineAccounting BodyInput where
  time := (storedCoinRoundOnline r eLoopState id (NativeCompiler.identity eLoopState)
    (commandExecutor r)).time
  workspace := (storedCoinRoundOnline r eLoopState id (NativeCompiler.identity eLoopState)
    (commandExecutor r)).workspace

private theorem storedCoinRound_resource_bound [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState))
    (input : StoredInput S) (OracleState : Type)
    (oracle : Fin external × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (coin : Bool) (state' : OracleState)
    (hcoin : (coin, state') ∈
      (ProbOracleComp.runWith oracle
        (ProbOracleComp.sample (ProbComp.uniform Bool)) state).support)
    (phase : OnlinePhase) :
    (storedCoinRoundArtifact r encState source sourceCompiler
        commandArtifact).online.time phase (input, coin) ≤
        (storedCoinRoundOnline r encState source sourceCompiler commandArtifact).time phase input ∧
      (storedCoinRoundArtifact r encState source sourceCompiler
        commandArtifact).online.workspace phase (input, coin) ≤
        (storedCoinRoundOnline r encState source sourceCompiler
          commandArtifact).workspace phase input := by
  cases coin
  · exact ⟨le_max_left _ _, le_max_left _ _⟩
  · exact ⟨le_max_right _ _, le_max_right _ _⟩

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
  exact storedCoinRound_resource_bound r eLoopState id
    (NativeCompiler.identity eLoopState) (commandExecutor r) input OracleState oracle state
      coin state' hcoin phase

private noncomputable def storedActiveArtifact [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState)) :=
  NativeOracleProgram.sequenceCaptured
    (NativeOracleProgram.fairBit (r := external) (eStoredInput encState))
    (storedCoinRoundArtifact r encState source sourceCompiler commandArtifact)
    (storedCoinRoundOnline r encState source sourceCompiler commandArtifact)
    (storedCoinRound_resource_bound r encState source sourceCompiler commandArtifact)

/-- Active source round: sample one retained fair bit, scan the runtime table once, then execute
the selected local or validated query command. -/
noncomputable def activeArtifact (r : ℕ) :=
  storedActiveArtifact r eLoopState id (NativeCompiler.identity eLoopState)
    (commandExecutor r)

private def storedActiveProgram [Inhabited S] (r : ℕ) (source : S → LoopState)
    (commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (input : StoredInput S) : WordOracleComp (Fin external) (StoredInput S) :=
  NativeOracleProgram.capturedProgram
    (fun _ : StoredInput S => ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun coinInput =>
      NativeOracleProgram.capturedProgram
        (fun input : StoredCoinInput S => pure (storedLookupResult source input))
        (fun lookupInput =>
          NativeOracleProgram.capturedProgram
            (fun input : StoredLookupInput S =>
              pure (commandFromStoredLookup r source input))
            (fun input => commandProgram (retainedCommandFromLookup r input)) lookupInput)
        coinInput)
    input

/-- Exact active-round semantics exposed to users of the generalized controller. -/
def activeProgramWithQueryBranch [Inhabited S] (r : ℕ) (source : S → LoopState)
    (update : S × ICfg → S)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (state : S) : WordOracleComp (Fin external) (Option S) :=
  storedActiveProgram r source (executeRetainedCommand r update queryProgram) (some state)

/-- An active round samples one fair bit, scans the source table once, constructs one command and
then either performs the supplied local update or invokes the retained query program. -/
theorem activeProgramWithQueryBranch_apply [Inhabited S] (r : ℕ) (source : S → LoopState)
    (update : S × ICfg → S)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (state : S) :
    activeProgramWithQueryBranch r source update queryProgram state = do
      let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
      let current := source state
      let commandInput := (current.desc, current.input, current.cfg, coin)
      let lookup := NativeCompiler.firstMatch (current.desc.table,
        current.cfg.key current.input ((current.cfg.control.getD none).getD 0))
      let command := commandAtFromLookup r (commandInput, lookup)
      match command with
      | .local cfg => pure (some (update (state, cfg)))
      | .query _ _ _ _ => queryProgram (state, command) :=
  rfl

/-! ### Outer one-round controller -/

private def storedBodyIsSome (input : StoredInput S) : List Bool := encTest input.isSome
private def storedBodyRemainingIsZero [Inhabited S] (source : S → LoopState)
    (input : StoredInput S) : List Bool :=
  encTest ((source (input.getD default)).remaining = 0)
private def storedBodyControlIsSome [Inhabited S] (source : S → LoopState)
    (input : StoredInput S) : List Bool :=
  encTest (source (input.getD default)).cfg.control.isSome

private noncomputable def storedBodyIsSomeCompiler (encState : S ↪ List Bool) :
    ClassifiedCompiler (storedBodyIsSome : StoredInput S → List Bool)
      (eStoredInput encState) encBits :=
  ClassifiedCompiler.inPhase .tags
    ((NativeCompiler.optionIsSomeTest encState).ofOutputEq fun _ => rfl)

private noncomputable def storedBodyRemainingIsZeroCompiler [Inhabited S]
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState) :
    ClassifiedCompiler (storedBodyRemainingIsZero source)
      (eStoredInput encState) encBits :=
  ClassifiedCompiler.inPhase .controller
    ((NativeCompiler.unaryIsZeroTest.comp
      (storedRemainingCompiler encState source sourceCompiler)).ofOutputEq fun _ => rfl)

private noncomputable def storedBodyControlIsSomeCompiler [Inhabited S]
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState) :
    ClassifiedCompiler (storedBodyControlIsSome source)
      (eStoredInput encState) encBits := by
  let control := ICfg.controlCompiler.comp
    (storedCfgCompiler encState source sourceCompiler)
  exact ClassifiedCompiler.inPhase .tags
    (((NativeCompiler.optionIsSomeTest Turing.MultiTapeTM.Universal.eSym).comp control).ofOutputEq
      fun _ => rfl)

private noncomputable def storedStopArtifact (external : ℕ) (encState : S ↪ List Bool) :=
  NativeOracleProgram.ofCompiler (r := external)
    (ClassifiedCompiler.inPhase .controller
      (NativeCompiler.const (eStoredInput encState) (eStoredInput encState) none))

private noncomputable def storedHaltedRoundArtifact [Inhabited S] (external : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState) :=
  NativeOracleProgram.ofCompiler (r := external)
    (ClassifiedCompiler.inPhase .controller
      (advanceStoredCompiler encState source sourceCompiler update updateCompiler))

/-- Semantics of one generalized retained controller round. Absent and exhausted states stop;
halted source storage is updated locally; active storage runs the shared coin/lookup/command
pipeline with the supplied query branch. -/
def bodyProgramWithQueryBranch [Inhabited S] (r : ℕ) (source : S → LoopState)
    (update : S × ICfg → S)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (input : Option S) : WordOracleComp (Fin external) (Option S) :=
  if storedBodyIsSome input = [] then pure none
  else if storedBodyRemainingIsZero source input = [] then
    if storedBodyControlIsSome source input = [] then
      pure (some (update (input.getD default, (source (input.getD default)).cfg)))
    else
      storedActiveProgram r source (executeRetainedCommand r update queryProgram) input
  else pure none

/-- An absent stored state remains absent without sampling or executing a command. -/
@[simp]
theorem bodyProgramWithQueryBranch_none [Inhabited S] (r : ℕ) (source : S → LoopState)
    (update : S × ICfg → S)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)) :
    bodyProgramWithQueryBranch r source update queryProgram none = pure none := by
  rfl

/-- Exhausted source fuel stops the controller before sampling or command execution. -/
theorem bodyProgramWithQueryBranch_exhausted [Inhabited S] (r : ℕ)
    (source : S → LoopState) (update : S × ICfg → S)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (state : S) (hremaining : (source state).remaining = 0) :
    bodyProgramWithQueryBranch r source update queryProgram (some state) = pure none := by
  simp [bodyProgramWithQueryBranch, storedBodyIsSome, storedBodyRemainingIsZero, hremaining]

/-- Halted source storage performs the supplied local state update without sampling. -/
theorem bodyProgramWithQueryBranch_halted [Inhabited S] (r : ℕ)
    (source : S → LoopState) (update : S × ICfg → S)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (state : S) (hremaining : (source state).remaining ≠ 0)
    (hcontrol : (source state).cfg.control = none) :
    bodyProgramWithQueryBranch r source update queryProgram (some state) =
      pure (some (update (state, (source state).cfg))) := by
  simp [bodyProgramWithQueryBranch, storedBodyIsSome, storedBodyRemainingIsZero,
    storedBodyControlIsSome, hremaining, hcontrol]

/-- Active source storage runs exactly the public fair-coin/lookup/command semantics above. -/
theorem bodyProgramWithQueryBranch_active [Inhabited S] (r : ℕ)
    (source : S → LoopState) (update : S × ICfg → S)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (state : S) (control : Option ℕ) (hremaining : (source state).remaining ≠ 0)
    (hcontrol : (source state).cfg.control = some control) :
    bodyProgramWithQueryBranch r source update queryProgram (some state) =
      activeProgramWithQueryBranch r source update queryProgram state := by
  simp [bodyProgramWithQueryBranch, activeProgramWithQueryBranch, storedBodyIsSome,
    storedBodyRemainingIsZero, storedBodyControlIsSome, hremaining, hcontrol]

private noncomputable def bodyWithCommandArtifact [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (commandArtifact : NativeOracleProgram external (executeRetainedCommand r update queryProgram)
      (eRetainedCommandInput r encState) (encOption encState)) :
    NativeOracleProgram external (bodyProgramWithQueryBranch r source update queryProgram)
      (encOption encState) (encOption encState) := by
  let active := storedActiveArtifact r encState source sourceCompiler commandArtifact
  let halted := storedHaltedRoundArtifact external encState source sourceCompiler update
    updateCompiler
  let byControl := NativeOracleProgram.dispatch
    (storedBodyControlIsSomeCompiler encState source sourceCompiler) active halted
  let byRemaining := NativeOracleProgram.dispatch
    (storedBodyRemainingIsZeroCompiler encState source sourceCompiler)
    (storedStopArtifact external encState) byControl
  let assembled := NativeOracleProgram.dispatch (storedBodyIsSomeCompiler encState)
    byRemaining (storedStopArtifact external encState)
  apply castProgram assembled
  funext input
  rfl

private theorem machine_bodyWithCommandArtifact [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (commandArtifact : NativeOracleProgram external (executeRetainedCommand r update queryProgram)
      (eRetainedCommandInput r encState) (encOption encState)) :
    (bodyWithCommandArtifact r encState source sourceCompiler update updateCompiler
      queryProgram commandArtifact).machine =
        let active := storedActiveArtifact r encState source sourceCompiler commandArtifact
        let halted := storedHaltedRoundArtifact external encState source sourceCompiler update
          updateCompiler
        let stop := storedStopArtifact external encState
        let byControl := NativeOracleProgram.dispatch
          (storedBodyControlIsSomeCompiler encState source sourceCompiler) active halted
        let byRemaining := NativeOracleProgram.dispatch
          (storedBodyRemainingIsZeroCompiler encState source sourceCompiler) stop byControl
        itePTM (ofDeterministic (storedBodyIsSomeCompiler encState).compiler.machine)
          byRemaining.machine stop.machine := by
  unfold bodyWithCommandArtifact
  rw [machine_castProgram]
  rfl

private theorem online_bodyWithCommandArtifact [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (commandArtifact : NativeOracleProgram external (executeRetainedCommand r update queryProgram)
      (eRetainedCommandInput r encState) (encOption encState)) :
    (bodyWithCommandArtifact r encState source sourceCompiler update updateCompiler
      queryProgram commandArtifact).online =
        let active := storedActiveArtifact r encState source sourceCompiler commandArtifact
        let halted := storedHaltedRoundArtifact external encState source sourceCompiler update
          updateCompiler
        let stop := storedStopArtifact external encState
        let byControl := NativeOracleProgram.dispatch
          (storedBodyControlIsSomeCompiler encState source sourceCompiler) active halted
        let byRemaining := NativeOracleProgram.dispatch
          (storedBodyRemainingIsZeroCompiler encState source sourceCompiler) stop byControl
        NativeOracleProgram.dispatchAccounting (storedBodyIsSomeCompiler encState)
          byRemaining stop := by
  unfold bodyWithCommandArtifact
  rw [online_castProgram]
  rfl

/-- The shared retained one-round controller with a supplied stateful query artifact. Source
commands use `Fin r`; the supplied artifact may expose a different external operation type. The
stored-state projection and local update are actual named compilers; lookup, coin, command-tag and
outer dispatch work remain the single native pipeline used by the ordinary interpreter. At
`r = 0` the uninhabited query branch and supplied query artifact are not installed. -/
noncomputable def bodyWithQueryBranch [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    {queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (queryArtifact : NativeOracleProgram external queryProgram
      (eRetainedCommandInput r encState) (encOption encState)) :
    NativeOracleProgram external (bodyProgramWithQueryBranch r source update queryProgram)
      (encOption encState) (encOption encState) := by
  cases r with
  | zero =>
      exact bodyWithCommandArtifact 0 encState source sourceCompiler update updateCompiler
        queryProgram (commandExecutorZeroWithQueryProgram encState update updateCompiler
          queryProgram)
  | succ r =>
      exact bodyWithCommandArtifact (r + 1) encState source sourceCompiler update updateCompiler
        queryProgram
        (commandExecutorWithQueryBranch (r + 1) encState update updateCompiler queryArtifact)

/-- The zero-channel controller installs only the local command executor; its retained machine is
independent of the uncallable supplied query artifact. -/
theorem machine_bodyWithQueryBranch_zero [Inhabited S]
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    {queryProgram : RetainedCommandInput 0 S → WordOracleComp (Fin external) (Option S)}
    (queryArtifact : NativeOracleProgram external queryProgram
      (eRetainedCommandInput 0 encState) (encOption encState)) :
    (bodyWithQueryBranch 0 encState source sourceCompiler update updateCompiler
      queryArtifact).machine =
        let command := commandExecutorZeroWithQueryProgram encState update updateCompiler
          queryProgram
        let active := storedActiveArtifact 0 encState source sourceCompiler command
        let halted := storedHaltedRoundArtifact external encState source sourceCompiler update
          updateCompiler
        let stop := storedStopArtifact external encState
        let byControl := NativeOracleProgram.dispatch
          (storedBodyControlIsSomeCompiler encState source sourceCompiler) active halted
        let byRemaining := NativeOracleProgram.dispatch
          (storedBodyRemainingIsZeroCompiler encState source sourceCompiler) stop byControl
        itePTM (ofDeterministic (storedBodyIsSomeCompiler encState).compiler.machine)
          byRemaining.machine stop.machine :=
  machine_bodyWithCommandArtifact 0 encState source sourceCompiler update updateCompiler
    queryProgram (commandExecutorZeroWithQueryProgram encState update updateCompiler queryProgram)

/-- Exact componentwise accounting of the zero-channel controller. -/
theorem online_bodyWithQueryBranch_zero [Inhabited S]
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    {queryProgram : RetainedCommandInput 0 S → WordOracleComp (Fin external) (Option S)}
    (queryArtifact : NativeOracleProgram external queryProgram
      (eRetainedCommandInput 0 encState) (encOption encState)) :
    (bodyWithQueryBranch 0 encState source sourceCompiler update updateCompiler
      queryArtifact).online =
        let command := commandExecutorZeroWithQueryProgram encState update updateCompiler
          queryProgram
        let active := storedActiveArtifact 0 encState source sourceCompiler command
        let halted := storedHaltedRoundArtifact external encState source sourceCompiler update
          updateCompiler
        let stop := storedStopArtifact external encState
        let byControl := NativeOracleProgram.dispatch
          (storedBodyControlIsSomeCompiler encState source sourceCompiler) active halted
        let byRemaining := NativeOracleProgram.dispatch
          (storedBodyRemainingIsZeroCompiler encState source sourceCompiler) stop byControl
        NativeOracleProgram.dispatchAccounting (storedBodyIsSomeCompiler encState)
          byRemaining stop :=
  online_bodyWithCommandArtifact 0 encState source sourceCompiler update updateCompiler
    queryProgram (commandExecutorZeroWithQueryProgram encState update updateCompiler queryProgram)

/-- For a nonempty channel type, the exact outer machine contains the one shared active pipeline
whose command executor dispatches to the supplied retained query artifact. -/
theorem machine_bodyWithQueryBranch_succ [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    {queryProgram : RetainedCommandInput (r + 1) S →
      WordOracleComp (Fin external) (Option S)}
    (queryArtifact : NativeOracleProgram external queryProgram
      (eRetainedCommandInput (r + 1) encState) (encOption encState)) :
    (bodyWithQueryBranch (r + 1) encState source sourceCompiler update updateCompiler
      queryArtifact).machine =
        let command := commandExecutorWithQueryBranch (r + 1) encState update updateCompiler
          queryArtifact
        let active := storedActiveArtifact (r + 1) encState source sourceCompiler command
        let halted := storedHaltedRoundArtifact external encState source sourceCompiler update
          updateCompiler
        let stop := storedStopArtifact external encState
        let byControl := NativeOracleProgram.dispatch
          (storedBodyControlIsSomeCompiler encState source sourceCompiler) active halted
        let byRemaining := NativeOracleProgram.dispatch
          (storedBodyRemainingIsZeroCompiler encState source sourceCompiler) stop byControl
        itePTM (ofDeterministic (storedBodyIsSomeCompiler encState).compiler.machine)
          byRemaining.machine stop.machine :=
  machine_bodyWithCommandArtifact (r + 1) encState source sourceCompiler update updateCompiler
    queryProgram
      (commandExecutorWithQueryBranch (r + 1) encState update updateCompiler queryArtifact)

/-- Exact componentwise accounting of the nonempty-channel controller. -/
theorem online_bodyWithQueryBranch_succ [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    {queryProgram : RetainedCommandInput (r + 1) S →
      WordOracleComp (Fin external) (Option S)}
    (queryArtifact : NativeOracleProgram external queryProgram
      (eRetainedCommandInput (r + 1) encState) (encOption encState)) :
    (bodyWithQueryBranch (r + 1) encState source sourceCompiler update updateCompiler
      queryArtifact).online =
        let command := commandExecutorWithQueryBranch (r + 1) encState update updateCompiler
          queryArtifact
        let active := storedActiveArtifact (r + 1) encState source sourceCompiler command
        let halted := storedHaltedRoundArtifact external encState source sourceCompiler update
          updateCompiler
        let stop := storedStopArtifact external encState
        let byControl := NativeOracleProgram.dispatch
          (storedBodyControlIsSomeCompiler encState source sourceCompiler) active halted
        let byRemaining := NativeOracleProgram.dispatch
          (storedBodyRemainingIsZeroCompiler encState source sourceCompiler) stop byControl
        NativeOracleProgram.dispatchAccounting (storedBodyIsSomeCompiler encState)
          byRemaining stop :=
  online_bodyWithCommandArtifact (r + 1) encState source sourceCompiler update updateCompiler
    queryProgram
      (commandExecutorWithQueryBranch (r + 1) encState update updateCompiler queryArtifact)

/-- The zero-channel retained machine and accounting do not depend on the supplied, uncallable
query artifact. -/
theorem bodyWithQueryBranch_zero_independent [Inhabited S]
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    {queryProgram : RetainedCommandInput 0 S → WordOracleComp (Fin external) (Option S)}
    (first : NativeOracleProgram external queryProgram
      (eRetainedCommandInput 0 encState) (encOption encState))
    (second : NativeOracleProgram external queryProgram
      (eRetainedCommandInput 0 encState) (encOption encState)) :
    (bodyWithQueryBranch 0 encState source sourceCompiler update updateCompiler first).machine =
        (bodyWithQueryBranch 0 encState source sourceCompiler update updateCompiler
          second).machine ∧
      (bodyWithQueryBranch 0 encState source sourceCompiler update updateCompiler first).online =
        (bodyWithQueryBranch 0 encState source sourceCompiler update updateCompiler
          second).online :=
  ⟨rfl, rfl⟩

/-- The complete generalized body is one installed composed description. -/
theorem bodyWithQueryBranch_installedDescriptions [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    {queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (queryArtifact : NativeOracleProgram external queryProgram
      (eRetainedCommandInput r encState) (encOption encState)) :
    (bodyWithQueryBranch r encState source sourceCompiler update updateCompiler
      queryArtifact).installedDescriptions =
        [(bodyWithQueryBranch r encState source sourceCompiler update updateCompiler
          queryArtifact).description] :=
  NativeOracleProgram.installedDescriptions_eq_singleton _

/-- The generalized body's one-occurrence installed charge is its final composed static size. -/
theorem bodyWithQueryBranch_installedBits [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    {queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (queryArtifact : NativeOracleProgram external queryProgram
      (eRetainedCommandInput r encState) (encOption encState)) :
    (bodyWithQueryBranch r encState source sourceCompiler update updateCompiler
      queryArtifact).installedBits =
        (bodyWithQueryBranch r encState source sourceCompiler update updateCompiler
          queryArtifact).staticBits :=
  NativeOracleProgram.installedBits_eq_staticBits _

/-- Retained one-round controller. Absent and zero-remaining states emit the empty option word;
halted source storage decrements the source clock without sampling; active storage executes the
coin/lookup/command pipeline. -/
noncomputable def body (r : ℕ) :
    NativeOracleProgram r (step r) eBodyInput eBodyInput := by
  let assembled := bodyWithQueryBranch r eLoopState id
    (NativeCompiler.identity eLoopState) (fun input => input.1.advance input.2)
    advanceCompiler (originalQueryArtifact r)
  apply castProgram assembled
  funext input
  cases input with
  | none => simp [step, bodyProgramWithQueryBranch, storedBodyIsSome]
  | some state =>
      by_cases hremaining : state.remaining = 0
      · simp [step, bodyProgramWithQueryBranch, storedBodyIsSome,
          storedBodyRemainingIsZero, hremaining]
      · cases hcontrol : state.cfg.control with
        | none =>
            simp [step, bodyProgramWithQueryBranch, storedBodyIsSome,
              storedBodyRemainingIsZero, storedBodyControlIsSome,
              hremaining, hcontrol, advance]
        | some control =>
            simp only [bodyProgramWithQueryBranch, storedBodyIsSome,
              storedBodyRemainingIsZero, storedBodyControlIsSome, hremaining, hcontrol,
              Option.isSome_some, encTest_apply, Bool.true_eq,
              List.replicate_one, List.cons_ne_nil, ↓reduceIte]
            cases r <;>
              simp [step, storedActiveProgram, executeRetainedCommand,
                NativeOracleProgram.capturedProgram, storedLookupResult,
                commandFromStoredLookup, retainedCommandFromLookup, originalQueryProgram,
                queryBranchProgram, NativeOracleProgram.queryTakeProgram, queryInput, queryPost,
                retainedCommandQueryPayload,
                defaultRetainedQueryPayload,
                commandAtFromLookup_firstMatch, hremaining, hcontrol]

/-! ### Finite proof reachability and uniform round bounds -/

/-- Replace only the dynamic round counter and first-order configuration of retained storage. -/
def LoopState.withDynamic (template : LoopState) (remaining : ℕ) (cfg : ICfg) : LoopState :=
  { template with remaining := remaining, cfg := cfg }

/-- Iterating the optional retained controller from positive dynamic storage is the corresponding
`wordStep` iteration, with the static fields retained and the round counter exhausted. -/
theorem iterate_step_withDynamic (r : ℕ) (template : LoopState) (cfg : ICfg) :
    ∀ count,
      OracleComp.iterate count (step r) (some (template.withDynamic count cfg)) =
        (fun final => some (template.withDynamic 0 final)) <$>
          OracleComp.iterate count
            (wordStep r template.desc template.input template.fuel template.replyBits) cfg
  | 0 => by simp [LoopState.withDynamic]
  | count + 1 => by
      rw [OracleComp.iterate_succ_bind, OracleComp.iterate_succ_bind]
      simp only [step, LoopState.withDynamic, Nat.succ_ne_zero, ↓reduceIte, advance]
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
        LoopState.withDynamic
          { desc := input.desc, input := input.input, fuel := input.fuel,
            replyBits := input.replyBits, remaining := input.fuel, cfg := ICfg.init input.desc }
          input.fuel (ICfg.init input.desc) by rfl]
    rw [iterate_step_withDynamic]
    simp [run, hcount, output, LoopState.withDynamic]
  · simp [stagedRun, initialState, hcount, rounds, output, run]

/-- Finite enumeration of every Boolean reply prefix whose length fits `replyBits`. -/
noncomputable def boundedReplyWords (replyBits : ℕ) : List (List Bool) :=
  (BitString.shortWords replyBits).toList

/-- The finite reply enumeration contains exactly the words within the copied-prefix budget. -/
theorem mem_boundedReplyWords_iff (reply : List Bool) (replyBits : ℕ) :
    reply ∈ boundedReplyWords replyBits ↔ reply.length ≤ replyBits := by
  rw [boundedReplyWords, Finset.mem_toList, BitString.mem_shortWords]

private def successorForReply (state : LoopState) (operation : Fin r) (next : ℕ)
    (pending : ICfg) (reply : List Bool) : BodyInput :=
  some (state.advance (pending.receive operation next
    ((unaryListDecoder.decode reply).take state.fuel)))

private noncomputable def coinSuccessors (r : ℕ) (state : LoopState) (coin : Bool) :
    List BodyInput :=
  match state.cfg.commandAt r state.desc state.input coin with
  | .local cfg => [some (state.advance cfg)]
  | .query operation _ next pending =>
      (boundedReplyWords state.replyBits).map
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
              have hprefix : reply.take current.replyBits ∈
                  boundedReplyWords current.replyBits := by
                exact (mem_boundedReplyWords_iff _ _).2 (List.length_take_le _ _)
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
  · cases initial <;> simp [Progress, LoopState.SameStatic]
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

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
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Decode

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Foundations.Data.BitString.ShortWords

import CslibFrontier.Languages.Probabilistic.Iteration.Reachable

/-!
# Retained fixed-channel oracle interpreter

The interpreter retains a finite-control `MultiTapePTM` for `run r`. It initializes the
runtime descriptor and input, samples a private bit on active instructions, scans the table
once per active instruction and dispatches a validated operation to a statically installed
query branch. The machine copies, decodes and installs the bounded reply prefix before
advancing. Its controller, codecs and finite dispatcher occur inside one installed description.
The source description remains part of the runtime input.

* `Turing.MultiTapePTM.Universal.NativeInterpreter.runWith_artifact_eq_runOracle` gives the
  exact joint law of the decoded result and the final state of an adaptive handler whose
  replies fit the copied prefix.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.time_artifact` gives the certified clock
  in terms of initialization, reachable state sizes, per-round bounds and output copying.
  It takes maxima over both private coins and all copied reply prefixes. These finite
  enumerations occur in the proof and clock specification.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.installed_add_input_bits` separates the
  installed descriptor, the framed source descriptor and the remaining runtime input.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.staticBits_polynomiallyBounded_of_schedules`
  gives a polynomial installed-size bound under explicit schedules for the exhaustive table
  and its coordinates. For fixed `r` the installed description is constant.

The native kernel certifies the sum of its phase allocations. Independent open-machine workspace
and a polynomial online clock derived from source input schedules remain open. A separately
installed handler must account for its own execution and description.

## References

The retained interpreter and its resource accounting are original to this module.
-/

public section

namespace Turing.MultiTapePTM.Universal.NativeInterpreter

open Cslib Cslib.Probability Turing.MultiTapeMachine Turing.MultiTapeTM
  Turing.MultiTapeTM.Internal Turing.MultiTapePTM.Internal
open Turing.MultiTapePTM.Universal

variable {S : Type} {r external : ℕ}

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
    (fun (desc, input, fuel, replyBits, remaining, cfg) =>
      ⟨desc, input, fuel, replyBits, remaining, cfg⟩)
    (fun state =>
      (state.desc, state.input, state.fuel, state.replyBits, state.remaining, state.cfg))
    (fun _ => rfl) fun _ => rfl

/-- Loop storage is absent on a channel-count mismatch. -/
@[expose] def initialState (r : ℕ) (input : RunInput) : Option LoopState :=
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
@[expose] def advance (state : LoopState) (cfg : ICfg) : LoopState :=
  { state with remaining := state.remaining - 1, cfg := cfg }

/-- Number of semantic source rounds selected by the initial typed state. -/
@[expose] def rounds : Option LoopState → ℕ
  | none => 0
  | some state => state.remaining

/-- One semantic loop round. The absent and zero-remaining cases are the encoded empty-word
terminator required by `boundedIterationEncodedOn`. A halted source configuration still consumes
one outer source round but draws no coin, exactly as `wordStep`. -/
@[expose] noncomputable def step (r : ℕ) :
    Option LoopState → WordOracleComp (Fin r) (Option LoopState)
  | none => pure none
  | some state =>
      if state.remaining = 0 then pure none
      else do
        let cfg ← wordStep r state.desc state.input state.fuel state.replyBits state.cfg
        pure (some (advance state cfg))

/-- Extract the interpreted output without conflating it with the generated static artifact or
the runtime input and supplied-description coordinates. -/
@[expose] def output : Option LoopState → List ℕ
  | none => []
  | some state => state.cfg.output

/-- Native-friendly staging of the exact fixed-channel semantics. -/
@[expose] noncomputable def stagedRun (r : ℕ) (input : RunInput) :
    WordOracleComp (Fin r) (List ℕ) := do
  let initial := initialState r input
  let final ← OracleComp.iterate (rounds initial) (step r) initial
  pure (output final)

/-! ### Concrete deterministic layouts -/

private abbrev eLoopTail4 := encPair encUnary eICfg
private abbrev eLoopTail3 := encPair encUnary eLoopTail4
private abbrev eLoopTail2 := encPair encUnary eLoopTail3
private abbrev eLoopTail1 := encPair (encList encUnary) eLoopTail2

private def loopFields (state : LoopState) :=
  (state.desc, state.input, state.fuel, state.replyBits, state.remaining, state.cfg)

private noncomputable def tail1Compiler :=
  (NativeCompiler.second eDesc eLoopTail1).ofInputEq (encIn := eLoopState) loopFields fun _ => rfl

private noncomputable def tail2Compiler :=
  (NativeCompiler.second (encList encUnary) eLoopTail2).comp tail1Compiler

private noncomputable def tail3Compiler :=
  (NativeCompiler.second encUnary eLoopTail3).comp tail2Compiler

private noncomputable def tail4Compiler :=
  (NativeCompiler.second encUnary eLoopTail4).comp tail3Compiler

private noncomputable def descCompiler : NativeCompiler LoopState.desc eLoopState eDesc :=
  ((NativeCompiler.first eDesc eLoopTail1).ofInputEq
    (encIn := eLoopState) loopFields fun _ => rfl).ofOutputEq fun _ => rfl

private noncomputable def inputCompiler :
    NativeCompiler LoopState.input eLoopState (encList encUnary) :=
  (NativeCompiler.first (encList encUnary) eLoopTail2).comp tail1Compiler

/-- Read the original source fuel from the retained loop state. -/
noncomputable opaque fuelCompiler : NativeCompiler LoopState.fuel eLoopState encUnary :=
  (NativeCompiler.first encUnary eLoopTail3).comp tail2Compiler

/-- Read the maximum number of copied reply bits from the retained loop state. -/
noncomputable opaque replyBitsCompiler : NativeCompiler LoopState.replyBits eLoopState encUnary :=
  (NativeCompiler.first encUnary eLoopTail4).comp tail3Compiler

private noncomputable def remainingCompiler :
    NativeCompiler LoopState.remaining eLoopState encUnary :=
  (NativeCompiler.first encUnary eICfg).comp tail4Compiler

/-- Read the current first-order configuration from the retained loop state. -/
noncomputable opaque cfgCompiler : NativeCompiler LoopState.cfg eLoopState eICfg :=
  (NativeCompiler.second encUnary eICfg).comp tail4Compiler

/-- Actual initializer for the optional typed loop state, including the runtime channel-count
test and the retained first-order blank-storage constructor. -/
noncomputable def initialCompiler (r : ℕ) :
    NativeCompiler (initialState r) eRunInput (encOption eLoopState) := by
  let runFields (input : RunInput) : Desc × (ℕ × (List ℕ × ℕ)) :=
    (input.desc, input.fuel, input.input, input.replyBits)
  let desc : NativeCompiler RunInput.desc eRunInput eDesc :=
    ((NativeCompiler.first eDesc eRunParameters).ofInputEq
      (encIn := eRunInput) runFields fun _ => rfl).ofOutputEq fun _ => rfl
  let fuel : NativeCompiler RunInput.fuel eRunInput encUnary :=
    (((NativeCompiler.first encUnary (encPair (encList encUnary) encUnary)).comp
      (NativeCompiler.second eDesc eRunParameters)).ofInputEq
        (encIn := eRunInput) runFields fun _ => rfl).ofOutputEq fun _ => rfl
  let sourceInput : NativeCompiler RunInput.input eRunInput (encList encUnary) :=
    (((NativeCompiler.first (encList encUnary) encUnary).comp
      ((NativeCompiler.second encUnary (encPair (encList encUnary) encUnary)).comp
        (NativeCompiler.second eDesc eRunParameters))).ofInputEq
          (encIn := eRunInput) runFields fun _ => rfl).ofOutputEq fun _ => rfl
  let replyBits : NativeCompiler RunInput.replyBits eRunInput encUnary :=
    (((NativeCompiler.second (encList encUnary) encUnary).comp
      ((NativeCompiler.second encUnary (encPair (encList encUnary) encUnary)).comp
        (NativeCompiler.second eDesc eRunParameters))).ofInputEq
          (encIn := eRunInput) runFields fun _ => rfl).ofOutputEq fun _ => rfl
  let operations := Desc.operationsCompiler.comp desc
  let countMatches := NativeCompiler.wordEqTest encUnary |>.comp
    (operations.pair (NativeCompiler.const eRunInput encUnary r))
  let cfg := ICfg.initCompiler.comp desc
  let fields := desc.pair
    (sourceInput.pair (fuel.pair (replyBits.pair (fuel.pair cfg))))
  let initializedState (input : RunInput) : LoopState :=
    ⟨input.desc, input.input, input.fuel, input.replyBits, input.fuel, ICfg.init input.desc⟩
  let initialized : NativeCompiler initializedState eRunInput eLoopState :=
    fields.ofOutputEq fun _ => rfl
  let present := (NativeCompiler.optionSome eLoopState).comp
    initialized
  let absent := NativeCompiler.const eRunInput (encOption eLoopState) none
  refine (NativeCompiler.ite countMatches present absent).ofOutputEq ?_
  intro input
  by_cases h : input.desc.operations = r <;> simp [initialState, initializedState, h]

private abbrev AdvanceInput := LoopState × ICfg
private def eAdvanceInput : AdvanceInput ↪ List Bool := encPair eLoopState eICfg

/-- Retained record update for one consumed source round. -/
noncomputable opaque advanceCompiler : NativeCompiler (fun input : LoopState × ICfg =>
    advance input.1 input.2) (encPair eLoopState eICfg) eLoopState := by
  let state := NativeCompiler.first eLoopState eICfg
  let cfg := NativeCompiler.second eLoopState eICfg
  let remaining := NativeCompiler.unaryPred.comp (remainingCompiler.comp state)
  let fields := (descCompiler.comp state).pair
    ((inputCompiler.comp state).pair
      ((fuelCompiler.comp state).pair
        ((replyBitsCompiler.comp state).pair (remaining.pair cfg))))
  exact fields.ofOutputEq fun _ => rfl

/-- Retained update wrapped in the nonempty option encoding used by the loop. -/
private noncomputable def advanceSomeCompiler : NativeCompiler (fun input : AdvanceInput =>
    some (advance input.1 input.2)) eAdvanceInput (encOption eLoopState) :=
  (NativeCompiler.optionSome eLoopState).comp advanceCompiler

private abbrev StoredInput (S : Type) := Option S
private abbrev eStoredInput (encState : S ↪ List Bool) : StoredInput S ↪ List Bool :=
  encOption encState
private abbrev StoredCoinInput (S : Type) := StoredInput S × Bool
private def eStoredCoinInput (encState : S ↪ List Bool) : StoredCoinInput S ↪ List Bool :=
  encPair (eStoredInput encState) encBool
private abbrev StoredLookupInput (S : Type) := StoredCoinInput S × Option Branches
private def eStoredLookupInput (encState : S ↪ List Bool) :
    StoredLookupInput S ↪ List Bool :=
  encPair (eStoredCoinInput encState) (encOption eBranches)

private abbrev BodyInput := StoredInput LoopState
private abbrev eBodyInput : BodyInput ↪ List Bool := eStoredInput eLoopState
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

private def toStoredCommandAtInput [Inhabited S] (source : S → LoopState)
    (input : StoredCoinInput S) : Desc × (List ℕ × (ICfg × Bool)) :=
  let state := source (input.1.getD default)
  (state.desc, state.input, state.cfg, input.2)

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
abbrev eRetainedCommandInput (r : ℕ) (encState : S ↪ List Bool) :
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

/-- A query command retains all four fields independently of the fallback operation. -/
theorem retainedCommandQueryPayload_query (state : S) (fallback operation : Fin r)
    (request : List ℕ) (next : ℕ) (pending : ICfg) :
    retainedCommandQueryPayload r fallback (state, .query operation request next pending) =
      ⟨operation, request, next, pending⟩ := by
  simp [retainedCommandQueryPayload, commandSumView]

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
      some (advance input.1
        (Sum.elim id (Function.const (RetainedQueryPayload r) default)
          (commandSumView r input.2))))
      (eCommandInput r) eBodyInput :=
  retainedLocalAdvanceCompiler r eLoopState (fun input => advance input.1 input.2)
    advanceCompiler

private noncomputable def queryPayloadFieldsCompiler (r : ℕ) (fallback : Fin r)
    (encState : S ↪ List Bool) :
    NativeCompiler
      (fun input : RetainedCommandInput r S =>
        let payload := retainedCommandQueryPayload r fallback input
        (payload.operation, payload.request, payload.next, payload.pending))
      (eRetainedCommandInput r encState)
      (encPair (eOperation r) (encPair (encList encUnary) (encPair encUnary eICfg))) :=
  let fields := fun payload : RetainedQueryPayload r =>
    (payload.operation, payload.request, payload.next, payload.pending)
  ((NativeCompiler.identity
      (encPair (eOperation r) (encPair (encList encUnary) (encPair encUnary eICfg))))
    |>.ofInputEq (encIn := eRetainedQueryPayload r) fields fun _ => rfl).comp
      (retainedCommandQueryPayloadCompiler r fallback encState)

/-- Select the operation tag from the retained command. -/
noncomputable opaque queryOperationCompiler (r : ℕ) (fallback : Fin r)
    (encState : S ↪ List Bool) :
    NativeCompiler
      (fun input : RetainedCommandInput r S =>
        (retainedCommandQueryPayload r fallback input).operation)
      (eRetainedCommandInput r encState) (eOperation r) :=
  (NativeCompiler.first (eOperation r)
    (encPair (encList encUnary) (encPair encUnary eICfg))).comp
      (queryPayloadFieldsCompiler r fallback encState)

private noncomputable def queryTailCompiler (r : ℕ) (fallback : Fin r)
    (encState : S ↪ List Bool) :
    NativeCompiler
      (fun input : RetainedCommandInput r S =>
        ((retainedCommandQueryPayload r fallback input).request,
          (retainedCommandQueryPayload r fallback input).next,
          (retainedCommandQueryPayload r fallback input).pending))
      (eRetainedCommandInput r encState) (encPair (encList encUnary) (encPair encUnary eICfg)) :=
  (NativeCompiler.second (eOperation r)
    (encPair (encList encUnary) (encPair encUnary eICfg))).comp
      (queryPayloadFieldsCompiler r fallback encState)

/-- Select the source request from the retained command. -/
noncomputable opaque queryRequestCompiler (r : ℕ) (fallback : Fin r)
    (encState : S ↪ List Bool) :
    NativeCompiler
      (fun input : RetainedCommandInput r S =>
        (retainedCommandQueryPayload r fallback input).request)
      (eRetainedCommandInput r encState) (encList encUnary) :=
  (NativeCompiler.first (encList encUnary) (encPair encUnary eICfg)).comp
    (queryTailCompiler r fallback encState)

private noncomputable def queryNextCfgCompiler (r : ℕ) (fallback : Fin r)
    (encState : S ↪ List Bool) :
    NativeCompiler
      (fun input : RetainedCommandInput r S =>
        ((retainedCommandQueryPayload r fallback input).next,
          (retainedCommandQueryPayload r fallback input).pending))
      (eRetainedCommandInput r encState) (encPair encUnary eICfg) :=
  (NativeCompiler.second (encList encUnary) (encPair encUnary eICfg)).comp
    (queryTailCompiler r fallback encState)

/-- Select the continuation tag from the retained command. -/
noncomputable opaque queryNextCompiler (r : ℕ) (fallback : Fin r)
    (encState : S ↪ List Bool) :
    NativeCompiler
      (fun input : RetainedCommandInput r S =>
        (retainedCommandQueryPayload r fallback input).next)
      (eRetainedCommandInput r encState) encUnary :=
  (NativeCompiler.first encUnary eICfg).comp (queryNextCfgCompiler r fallback encState)

/-- Select the suspended source configuration from the retained command. -/
noncomputable opaque queryCfgCompiler (r : ℕ) (fallback : Fin r)
    (encState : S ↪ List Bool) :
    NativeCompiler
      (fun input : RetainedCommandInput r S =>
        (retainedCommandQueryPayload r fallback input).pending)
      (eRetainedCommandInput r encState) eICfg :=
  (NativeCompiler.second encUnary eICfg).comp (queryNextCfgCompiler r fallback encState)

private noncomputable def queryRequestWordCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r =>
        encList encUnary (retainedCommandQueryPayload r fallback input).request)
      (eCommandInput r) encBits :=
  (queryRequestCompiler r fallback eLoopState).ofOutputEq fun _ => rfl

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
private noncomputable def queryInputCompiler (r : ℕ) (fallback : Fin r) :
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
  some (advance state (payload.pending.receive payload.operation payload.next decoded))

/-- Phase-preserving deterministic reply decoding, source-symbol truncation, checked reply
installation and loop-state update. -/
private noncomputable def queryPostCompiler (r : ℕ) (fallback : Fin r) : ClassifiedCompiler
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
    (queryOperationCompiler r fallback eLoopState)).comp command
  let next := (ClassifiedCompiler.inPhase .tags
    (queryNextCompiler r fallback eLoopState)).comp command
  let cfg := (ClassifiedCompiler.inPhase .parsing
    (queryCfgCompiler r fallback eLoopState)).comp command
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
private noncomputable def preparedQuery (r : ℕ) (fallback operation : Fin r) :=
  NativeOracleProgram.preprocess
    (ClassifiedCompiler.inPhase .marshalling (queryInputCompiler r fallback))
    (NativeOracleProgram.queryTake operation)

/-- Deterministic retained reply pipeline. -/
private noncomputable def queryPostArtifact (r : ℕ) (fallback : Fin r) :=
  NativeOracleProgram.ofCompiler (r := r) (queryPostCompiler r fallback)

/-- Possible copied prefixes, enumerated only to choose a common clock. -/
noncomputable def boundedReplyWords (replyBits : ℕ) : List (List Bool) :=
  (BitString.shortWords replyBits).toList

theorem mem_boundedReplyWords_iff (reply : List Bool) (replyBits : ℕ) :
    reply ∈ boundedReplyWords replyBits ↔ reply.length ≤ replyBits := by
  simp [boundedReplyWords, BitString.mem_shortWords]

/-- Uniform phase bounds for the deterministic post-query pipeline over every copied reply prefix
that the external handler can produce. -/
private noncomputable def queryPostOnline (r : ℕ) (fallback : Fin r) :
    OnlineAccounting (CommandInput r) where
  time := fun phase input =>
    listMax (fun reply =>
      (queryPostArtifact r fallback).online.time phase (input, reply))
      (boundedReplyWords (commandState input).replyBits)

private theorem queryPostOnline_le (r : ℕ) (fallback : Fin r)
    (input : CommandInput r) (reply : List Bool)
    (hreply : reply.length ≤ (commandState input).replyBits) (phase : OnlinePhase) :
    (queryPostArtifact r fallback).online.time phase (input, reply) ≤
        (queryPostOnline r fallback).time phase input := by
  have hmem : reply ∈ boundedReplyWords (commandState input).replyBits := by
    exact (mem_boundedReplyWords_iff _ _).2 hreply
  exact le_listMax (f := fun reply =>
    (queryPostArtifact r fallback).online.time phase (input, reply)) hmem

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
        (queryPostOnline r fallback).time phase input := by
  have hlength : reply.length ≤ (queryInput r fallback input).2 := by
    rw [NativeOracleProgram.queryTakeProgram, ProbOracleComp.runWith_map] at hreply
    obtain ⟨⟨rawReply, replyState⟩, -, heq⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp hreply
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact List.length_take_le _ _
  exact queryPostOnline_le r fallback input reply hlength phase

/-- Stateful semantics of one validated fixed-operation query and its retained reply pipeline. -/
private noncomputable def queryBranchProgram (r : ℕ) (fallback operation : Fin r)
    (input : CommandInput r) : WordOracleComp (Fin r) BodyInput :=
  NativeOracleProgram.capturedProgram
    (fun command =>
      NativeOracleProgram.queryTakeProgram operation (queryInput r fallback command))
    (fun postInput => pure (queryPost r fallback postInput)) input

/-- One actual fixed-operation query branch. -/
private noncomputable def queryBranch (r : ℕ) (fallback operation : Fin r) :
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
  (queryOperationCompiler r fallback eLoopState).ofOutputEq fun _ => rfl

/-- Retained equality test for one statically installed operation branch. -/
private noncomputable def operationTestCompiler (r : ℕ) (fallback operation : Fin r) :
    ClassifiedCompiler (operationTest r fallback operation) (eCommandInput r) encBits := by
  let compared := (operationNatCompiler r fallback).pair
    (NativeCompiler.const (eCommandInput r) encUnary operation.val)
  exact ClassifiedCompiler.inPhase .tags
    ((NativeCompiler.wordEqTest encUnary).comp compared |>.ofOutputEq fun input => by
      simp only [operationTest, encBits_apply, encUnary.injective.eq_iff, Fin.ext_iff,
        Function.const_apply])

/-- One case of the fixed finite operation dispatcher. -/
private noncomputable def operationCase (r : ℕ) (fallback operation : Fin r) :
    NativeOracleProgram.DispatchCase r (CommandInput r) BodyInput
      (eCommandInput r) eBodyInput where
  test := operationTest r fallback operation
  condition := operationTestCompiler r fallback operation
  program := queryBranchProgram r fallback operation
  branch := queryBranch r fallback operation

/-- Explicit operation order used by the retained finite dispatcher. -/
private def operations (r : ℕ) : List (Fin r) := List.finRange r

/-- Fallback is unreachable for a well-typed query command, but remains an actual deterministic
artifact. It advances the original state with the explicit local default rather than invoking a
semantic callback. -/
private def localAdvance (r : ℕ) (input : CommandInput r) : BodyInput :=
  some (advance (commandState input)
    (Sum.elim id (Function.const (RetainedQueryPayload r) default)
      (commandSumView r input.2)))

private noncomputable def queryFallback (r : ℕ) :=
  NativeOracleProgram.ofCompiler (r := r)
    (ClassifiedCompiler.inPhase .controller (localAdvanceCompiler r))

/-- Actual finite fixed-operation dispatcher. For `r = 0` the case list is empty. -/
private noncomputable def queryDispatch (r : ℕ) (fallback : Fin r) :=
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
    ((retainedCommandIsQueryCompiler r encState).ofOutputEq (encOut := encBits)
      (g := fun input : RetainedCommandInput r S => encTest (commandSumView r input.2).isRight)
      fun _ => rfl)
  let assembled := NativeOracleProgram.dispatch condition queryArtifact
    (retainedLocalArtifact external r encState update updateCompiler)
  apply castProgram assembled
  funext input
  obtain ⟨state, command⟩ := input
  cases command <;> simp [executeRetainedCommand, commandSumView, encTest_false, encTest_true]

private noncomputable def commandExecutorZeroWithQueryProgram
    (encState : S ↪ List Bool) (update : S × ICfg → S)
    (updateCompiler : NativeCompiler update (encPair encState eICfg) encState)
    (queryProgram : RetainedCommandInput 0 S → WordOracleComp (Fin external) (Option S)) :
    NativeOracleProgram external (executeRetainedCommand 0 update queryProgram)
      (eRetainedCommandInput 0 encState) (encOption encState) := by
  let localProgram := retainedLocalArtifact external 0 encState update updateCompiler
  apply castProgram localProgram
  funext input
  obtain ⟨state, command⟩ := input
  cases command with
  | «local» cfg => rfl
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
  clear hops
  induction operationList with
  | nil => simp at hmem
  | cons head tail ih =>
      rw [List.map_cons, NativeOracleProgram.dispatchProgram]
      by_cases h : head = operation
      · subst head
        simp only [operationCase, operationTest, hoperation, decide_true, encTest_true,
          List.cons_ne_nil, ↓reduceIte]
      · have hne : operation ≠ head := fun hop => h hop.symm
        have htail : operation ∈ tail := (List.mem_cons.mp hmem).resolve_left hne
        simp only [operationCase, operationTest, hoperation, hne, decide_false, encTest_false,
          ↓reduceIte]
        exact ih htail

private noncomputable def originalQueryProgram : (r : ℕ) →
    RetainedCommandInput r LoopState → WordOracleComp (Fin r) BodyInput
  | 0, input => pure (localAdvance 0 input)
  | r + 1, input =>
      match input.2 with
      | .local _ => queryBranchProgram (r + 1) 0 0 input
      | .query operation _ _ _ => queryBranchProgram (r + 1) 0 operation input

private noncomputable def originalQueryArtifact : (r : ℕ) →
    NativeOracleProgram r (originalQueryProgram r) (eCommandInput r) eBodyInput
  | 0 => queryFallback 0
  | r + 1 => by
      -- The outer command test intercepts local commands before this dispatcher.
      apply castProgram (queryDispatch (r + 1) 0)
      funext input
      obtain ⟨state, command⟩ := input
      cases command with
      | «local» cfg =>
          exact dispatchProgram_operations (r + 1) 0 0 (state, .local cfg) rfl
      | query operation request next pending =>
          exact dispatchProgram_operations (r + 1) 0 operation
            (state, .query operation request next pending) rfl

/-! ### Single-lookup active round -/

private def storedLookupResult [Inhabited S] (source : S → LoopState)
    (input : StoredCoinInput S) : Option Branches :=
  let commandInput := toStoredCommandAtInput source input
  NativeCompiler.firstMatch (commandInput.1.table,
    commandInput.2.2.1.key commandInput.2.1
      ((commandInput.2.2.1.control.getD none).getD 0))

private noncomputable def storedLookupArtifact [Inhabited S] (external : ℕ)
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

private def commandFromStoredLookup [Inhabited S] (r : ℕ) (source : S → LoopState)
    (input : StoredLookupInput S) : Command r :=
  commandAtFromLookup r (toStoredCommandAtInput source input.1, input.2)

private noncomputable def commandFromStoredLookupArtifact [Inhabited S] (external r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState) :
    NativeOracleProgram external
      (fun input : StoredLookupInput S => pure (commandFromStoredLookup r source input))
      (eStoredLookupInput encState) (eCommand r) :=
  NativeOracleProgram.ofCompiler (r := external)
    (ClassifiedCompiler.inPhase .localStep
      (storedCommandCompiler r encState source sourceCompiler))

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

private noncomputable def storedCommandExecutorOnline [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState)) :
    OnlineAccounting (StoredLookupInput S) :=
  (preparedCommandArtifact r encState commandArtifact).online.reindex fun input =>
    (input, commandFromStoredLookup r source input)

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
        (storedCommandExecutorOnline r encState source commandArtifact).time phase input := by
  simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hcommand
  rcases hcommand with ⟨rfl, rfl⟩
  exact le_rfl

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

private noncomputable def storedFromLookupOnline [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState)) :
    OnlineAccounting (StoredCoinInput S) :=
  (fromStoredLookupArtifact r encState source sourceCompiler commandArtifact).online.reindex
    fun input => (input, storedLookupResult source input)

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
          input := by
  simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hlookup
  rcases hlookup with ⟨rfl, rfl⟩
  exact le_rfl

private noncomputable def storedCoinRoundArtifact [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState)) :=
  NativeOracleProgram.sequenceCaptured
    (storedLookupArtifact external encState source sourceCompiler)
    (fromStoredLookupArtifact r encState source sourceCompiler commandArtifact)
    (storedFromLookupOnline r encState source sourceCompiler commandArtifact)
    (storedFromLookup_resource_bound r encState source sourceCompiler commandArtifact)

private noncomputable def storedCoinRoundOnline [Inhabited S] (r : ℕ)
    (encState : S ↪ List Bool) (source : S → LoopState)
    (sourceCompiler : NativeCompiler source encState eLoopState)
    {commandProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S)}
    (commandArtifact : NativeOracleProgram external commandProgram
      (eRetainedCommandInput r encState) (encOption encState)) :
    OnlineAccounting (StoredInput S) where
  time := fun phase input =>
    max ((storedCoinRoundArtifact r encState source sourceCompiler
        commandArtifact).online.time phase (input, false))
      ((storedCoinRoundArtifact r encState source sourceCompiler
        commandArtifact).online.time phase (input, true))


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
        (storedCoinRoundOnline r encState source sourceCompiler commandArtifact).time
          phase input := by
  cases coin
  · exact le_max_left _ _
  · exact le_max_right _ _

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

private noncomputable def storedActiveProgram [Inhabited S] (r : ℕ) (source : S → LoopState)
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
noncomputable def activeProgramWithQueryBranch [Inhabited S] (r : ℕ) (source : S → LoopState)
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
    activeProgramWithQueryBranch r source update queryProgram state = (do
      let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
      let current := source state
      let command := current.cfg.commandAt r current.desc current.input coin
      match command with
      | .local cfg => pure (some (update (state, cfg)))
      | .query _ _ _ _ => queryProgram (state, command)) := by
  simp only [activeProgramWithQueryBranch, storedActiveProgram, NativeOracleProgram.capturedProgram,
    pure_bind, storedLookupResult, commandFromStoredLookup, toStoredCommandAtInput,
    retainedCommandFromLookup, Option.getD_some]
  apply OracleComp.bind_congr_on_support
  intro coin _
  rw [commandAtFromLookup_firstMatch r
    ((source state).desc, (source state).input, (source state).cfg, coin)]
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
noncomputable def bodyProgramWithQueryBranch [Inhabited S] (r : ℕ) (source : S → LoopState)
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
  simp [bodyProgramWithQueryBranch, storedBodyIsSome, storedBodyRemainingIsZero,
    hremaining, encTest_true]

/-- Halted source storage performs the supplied local state update without sampling. -/
theorem bodyProgramWithQueryBranch_halted [Inhabited S] (r : ℕ)
    (source : S → LoopState) (update : S × ICfg → S)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (state : S) (hremaining : (source state).remaining ≠ 0)
    (hcontrol : (source state).cfg.control = none) :
    bodyProgramWithQueryBranch r source update queryProgram (some state) =
      pure (some (update (state, (source state).cfg))) := by
  simp [bodyProgramWithQueryBranch, storedBodyIsSome, storedBodyRemainingIsZero,
    storedBodyControlIsSome, hremaining, hcontrol, encTest_true, encTest_false]

/-- Active source storage runs exactly the public fair-coin/lookup/command semantics above. -/
theorem bodyProgramWithQueryBranch_active [Inhabited S] (r : ℕ)
    (source : S → LoopState) (update : S × ICfg → S)
    (queryProgram : RetainedCommandInput r S → WordOracleComp (Fin external) (Option S))
    (state : S) (control : Option ℕ) (hremaining : (source state).remaining ≠ 0)
    (hcontrol : (source state).cfg.control = some control) :
    bodyProgramWithQueryBranch r source update queryProgram (some state) =
      activeProgramWithQueryBranch r source update queryProgram state := by
  simp [bodyProgramWithQueryBranch, activeProgramWithQueryBranch, storedBodyIsSome,
    storedBodyRemainingIsZero, storedBodyControlIsSome, hremaining, hcontrol, encTest_true,
    encTest_false]

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

/-- Retained one-round controller. Absent and zero-remaining states emit the empty option word;
halted source storage decrements the source clock without sampling; active storage executes the
coin/lookup/command pipeline. -/
private noncomputable def body (r : ℕ) :
    NativeOracleProgram r (step r) eBodyInput eBodyInput := by
  let assembled := bodyWithQueryBranch r eLoopState id
    (NativeCompiler.identity eLoopState) (fun input => advance input.1 input.2)
    advanceCompiler (originalQueryArtifact r)
  apply castProgram assembled
  funext input
  cases input with
  | none => rfl
  | some state =>
      by_cases hremaining : state.remaining = 0
      · rw [bodyProgramWithQueryBranch_exhausted (hremaining := hremaining)]
        simp [step, hremaining]
      · cases hcontrol : state.cfg.control with
        | none =>
            rw [bodyProgramWithQueryBranch_halted (hremaining := hremaining) (hcontrol := hcontrol)]
            simp [step, hremaining, wordStep, hcontrol]
        | some control =>
            rw [bodyProgramWithQueryBranch_active (hremaining := hremaining) (hcontrol := hcontrol),
              activeProgramWithQueryBranch_apply]
            simp only [step, hremaining, ↓reduceIte, wordStep, hcontrol, id_eq]
            conv_rhs => rw [bind_assoc]
            apply OracleComp.bind_congr_on_support
            intro coin _
            cases hcmd : state.cfg.commandAt r state.desc state.input coin with
            | «local» next => simp
            | query operation request next pending =>
                cases r with
                | zero => exact Fin.elim0 operation
                | succ r =>
                    simp [originalQueryProgram, queryBranchProgram,
                      NativeOracleProgram.capturedProgram, NativeOracleProgram.queryTakeProgram,
                      queryInput, queryPost, commandState,
                      retainedCommandQueryPayload, commandSumView, unaryListDecoder,
                      Turing.MultiTapeTM.Decoder.list, Turing.MultiTapeTM.Decoder.unary]

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
      rw [map_eq_bind_pure_comp]
      conv_lhs => rw [bind_assoc]
      conv_rhs => rw [bind_assoc]
      simp only [pure_bind]
      apply OracleComp.bind_congr_on_support
      intro next _
      change OracleComp.iterate count (step r)
        (some (LoopState.withDynamic template count next)) = _
      rw [iterate_step_withDynamic r template next count]
      rw [map_eq_bind_pure_comp]
      rfl

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
private def successorForReply (state : LoopState) (operation : Fin r) (next : ℕ)
    (pending : ICfg) (reply : List Bool) : BodyInput :=
  some (advance state (pending.receive operation next
    ((unaryListDecoder.decode reply).take state.fuel)))

private noncomputable def coinSuccessors (r : ℕ) (state : LoopState) (coin : Bool) :
    List BodyInput :=
  match state.cfg.commandAt r state.desc state.input coin with
  | .local cfg => [some (advance state cfg)]
  | .query operation _ next pending =>
      (boundedReplyWords state.replyBits).map
        (successorForReply state operation next pending)

/-- Finite overapproximation of all one-round results under arbitrary stateful handlers. Duplicate
states are harmless and keep the proof enumeration independent of `DecidableEq LoopState`. -/
private noncomputable def successors (r : ℕ) : BodyInput → List BodyInput
  | none => [none]
  | some state =>
      if state.remaining = 0 then [none]
      else match state.cfg.control with
        | none => [some (advance state state.cfg)]
        | some _ => [false, true].flatMap (coinSuccessors r state)

/-- States reachable after exactly `count` semantic rounds in the proof enumeration. -/
private noncomputable abbrev reachable (r : ℕ) :=
  ProbOracleComp.reachableIn (successors r)

/-- All reachable typed states at indices used by the bounded-iteration certificate. -/
private noncomputable abbrev reachablePrefix (r : ℕ) (initial : BodyInput) : List BodyInput :=
  ProbOracleComp.reachableThrough (successors r) initial (rounds initial)

private theorem support_mem_successors (r : ℕ) (current next : BodyInput)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state state' : OracleState)
    (hnext : (next, state') ∈
      (ProbOracleComp.runWith oracle (step r current) state).support) :
    next ∈ successors r current := by
  rcases current with _ | current
  · supp_cases hnext [step, ProbOracleComp.runWith_pure] with ⟨rfl, rfl⟩
    simp [successors]
  · by_cases hremaining : current.remaining = 0
    · supp_cases hnext [step, hremaining, ProbOracleComp.runWith_pure] with ⟨rfl, rfl⟩
      simp [successors, hremaining]
    · rw [step, ite_eq_right hremaining, ProbOracleComp.runWith_bind] at hnext
      obtain ⟨⟨nextCfg, nextState⟩, hcfg, hfinal⟩ :=
        (PMF.mem_support_bind_iff _ _ _).mp hnext
      supp_cases hfinal [ProbOracleComp.runWith_pure] with ⟨rfl, rfl⟩
      cases hcontrol : current.cfg.control with
      | none =>
          supp_cases hcfg [wordStep, hcontrol, ProbOracleComp.runWith_pure] with ⟨rfl, rfl⟩
          simp [successors, hremaining, hcontrol]
      | some control =>
          rw [wordStep, hcontrol, ProbOracleComp.runWith_bind] at hcfg
          obtain ⟨⟨coin, coinState⟩, hcoin, hcommand⟩ :=
            (PMF.mem_support_bind_iff _ _ _).mp hcfg
          have hcoinValue : coin = false ∨ coin = true := by cases coin <;> simp
          cases hcmd : current.cfg.commandAt r current.desc current.input coin with
          | «local» cfg =>
              supp_cases hcommand [hcmd, ProbOracleComp.runWith_pure] with ⟨rfl, rfl⟩
              have hbranch : some (advance current nextCfg) ∈ coinSuccessors r current coin := by
                simp [coinSuccessors, hcmd]
              have hall : some (advance current nextCfg) ∈
                  [false, true].flatMap (coinSuccessors r current) :=
                List.mem_flatMap.mpr ⟨coin, by simp [hcoinValue], hbranch⟩
              simpa only [successors, hremaining, hcontrol, ↓reduceIte] using hall
          | query operation request nextTag pending =>
              rw [hcmd, ProbOracleComp.runWith_bind] at hcommand
              obtain ⟨⟨reply, replyState⟩, hreply, hfinal⟩ :=
                (PMF.mem_support_bind_iff _ _ _).mp hcommand
              supp_cases hfinal [ProbOracleComp.runWith_pure] with ⟨rfl, rfl⟩
              have hprefix :
                  reply.take current.replyBits ∈ boundedReplyWords current.replyBits := by
                exact (mem_boundedReplyWords_iff _ _).2 (List.length_take_le _ _)
              have hbranch :
                  some
                    (advance current
                      (pending.receive operation nextTag
                        ((unaryListDecoder.decode
                          (reply.take current.replyBits)).take current.fuel))) ∈
                    coinSuccessors r current coin := by
                simp only [coinSuccessors, hcmd, List.mem_map]
                exact ⟨reply.take current.replyBits, hprefix, rfl⟩
              have hall :
                  some
                    (advance current
                      (pending.receive operation nextTag
                        ((unaryListDecoder.decode
                          (reply.take current.replyBits)).take current.fuel))) ∈
                    [false, true].flatMap (coinSuccessors r current) :=
                List.mem_flatMap.mpr ⟨coin, by simp [hcoinValue], hbranch⟩
              simpa only [successors, hremaining, hcontrol, ↓reduceIte] using hall

private theorem support_mem_reachable (r : ℕ) (initial : BodyInput) (count : ℕ)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (current : BodyInput) (state' : OracleState)
    (hcurrent : (current, state') ∈
      (ProbOracleComp.runWith oracle
        (OracleComp.iterate count (step r) initial) state).support) :
    current ∈ reachable r initial count :=
  ProbOracleComp.mem_reachableIn_of_runWith_iterate (step r) (successors r) oracle
    (fun a b s t => support_mem_successors r a b OracleState oracle s t)
      initial count state hcurrent

private def Progress (initial : BodyInput) (count : ℕ) (current : BodyInput) : Prop :=
  match initial with
  | none => current = none
  | some first => ∃ second, current = some second ∧ LoopState.SameStatic first second ∧
      second.remaining + count = first.remaining

/-- Reachability plus the exact remaining-round equation. -/
private def Invariant (r : ℕ) (initial : BodyInput) (count : ℕ) (current : BodyInput) : Prop :=
  Progress initial count current ∧ current ∈ reachable r initial count

private theorem invariant_zero (r : ℕ) (initial : BodyInput) :
    Invariant r initial 0 initial := by
  constructor
  · cases initial with
    | none => rfl
    | some state => exact ⟨state, rfl, ⟨rfl, rfl, rfl, rfl⟩, by simp⟩
  · simp [reachable, ProbOracleComp.reachableIn]

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
      have hrounds : rounds initial = first.remaining := by simp [hinitial, rounds]
      have hpositive : second.remaining ≠ 0 := by omega
      rw [step, ite_eq_right hpositive, ProbOracleComp.runWith_bind] at hnext
      obtain ⟨⟨nextCfg, nextState⟩, hcfg, hfinal⟩ :=
        (PMF.mem_support_bind_iff _ _ _).mp hnext
      supp_cases hfinal [ProbOracleComp.runWith_pure] with ⟨rfl, rfl⟩
      constructor
      · refine ⟨advance second nextCfg, rfl, ?_, ?_⟩
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
  exact ProbOracleComp.mem_reachableIn_succ hinvariant.2
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
      have hcurrent : current = none := by
        simpa only [Progress, hinitial] using hinvariant.1
      subst current
      simp [step]
  | some first =>
      simp only [hinitial, rounds] at hinvariant
      obtain ⟨second, rfl, hstatic, hremaining⟩ := hinvariant.1
      have hzero : second.remaining = 0 := by omega
      simp [step, hzero]

/-- Maximum encoded typed-state length over every finitely enumerated reachable prefix state. -/
private noncomputable def lengthBound (r : ℕ) (initial : BodyInput) : ℕ :=
  listMax (fun state => (encOption eLoopState state).length) (reachablePrefix r initial)

/-- Phasewise maximum of the retained body over every finitely enumerated reachable prefix state. -/
private noncomputable def roundOnline (r : ℕ) : OnlineAccounting BodyInput where
  time := fun phase initial =>
    listMax (fun current => (body r).online.time phase current) (reachablePrefix r initial)

private theorem body_resource_bound (r : ℕ) (initial : BodyInput) (count : ℕ)
    (hcount : count ≤ rounds initial) (current : BodyInput)
    (hinvariant : Invariant r initial count current) (phase : OnlinePhase) :
    (body r).online.time phase current ≤ (roundOnline r).time phase initial := by
  have hmem := ProbOracleComp.mem_reachableThrough hcount hinvariant.2
  exact le_listMax hmem

private theorem state_length_bound (r : ℕ) (initial : BodyInput) (count : ℕ)
    (hcount : count ≤ rounds initial) (current : BodyInput)
    (hinvariant : Invariant r initial count current) :
    (encOption eLoopState current).length ≤ lengthBound r initial :=
  le_listMax (f := fun state => (encOption eLoopState state).length)
    (ProbOracleComp.mem_reachableThrough hcount hinvariant.2)

/-! ### Complete retained artifact -/

/-- Retained typed loop with runtime-indexed clock, state-length and per-phase bounds. -/
private noncomputable def loopArtifact (r : ℕ) :=
  NativeOracleProgram.boundedIterationEncodedOn (.option loopStateDecoder) (body r) rounds
    (lengthBound r) (roundOnline r) (Invariant r) (invariant_zero r)
    (body_resource_bound r)
    (fun _initial _count hcount _current hinvariant OracleState oracle state state' _next hnext =>
      invariant_successor hcount hinvariant OracleState oracle state state' hnext)
    (invariant_last r) (state_length_bound r)

private noncomputable def classifiedInitial (r : ℕ) :=
  ClassifiedCompiler.inPhase .inputCopy (initialCompiler r)

/-- Copy and initialize the encoded runtime input before the fixed loop machine. -/
private noncomputable def initializedLoop (r : ℕ) :=
  NativeOracleProgram.preprocess (classifiedInitial r) (loopArtifact r)

private noncomputable def outputCompiler :
    NativeCompiler output eBodyInput (encList encUnary) := by
  let state := bodyStateCompiler
  exact (ICfg.outputCompiler.comp (cfgCompiler.comp state)).ofOutputEq fun input => by
    cases input <;> rfl

/-- Reachability maximum for the output-copy compiler on final loop results. -/
private noncomputable def outputOnline (r : ℕ) : OnlineAccounting RunInput where
  time := fun phase input =>
    listMax (fun current =>
      (ClassifiedCompiler.inPhase .outputCopy outputCompiler).online.time phase current)
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
        (outputOnline r).time phase input := by
  have hreach := support_mem_reachable r (initialState r input)
    (rounds (initialState r input)) OracleState oracle state current state' hcurrent
  exact le_listMax hreach

/-- Complete fixed-channel retained interpreter before the extensional source-semantics cast. -/
private noncomputable def stagedArtifact (r : ℕ) :
    NativeOracleProgram r (stagedRun r) eRunInput (encList encUnary) :=
  castProgram
    (NativeOracleProgram.postprocess (initializedLoop r)
      (ClassifiedCompiler.inPhase .outputCopy outputCompiler) (outputOnline r)
      (output_resource_bound r)) (by
        funext input
        rw [stagedRun, map_eq_bind_pure_comp]
        apply OracleComp.bind_congr_on_support
        intro final _
        rfl)

/-- Complete actual finite-control interpreter for `run r`. -/
@[irreducible] noncomputable def artifact (r : ℕ) :
    NativeOracleProgram r (run r) eRunInput (encList encUnary) :=
  castProgram (stagedArtifact r) (stagedRun_eq_run r)

/-- The data-dependent bounds used to choose the interpreter clock. -/
structure ClockBounds where
  /-- Sum of the per-phase maxima of the retained body, over reachable prefix states. -/
  roundTime : ℕ
  /-- Largest encoded loop state in the finite reachability enumeration. -/
  stateBits : ℕ
  /-- Sum of the output compiler's phase maxima over reachable final states. -/
  outputTime : ℕ

/-- Bounds for the supplied descriptor, fuel, input and maximum copied reply prefix.
The enumeration covers both coin outcomes and every copied prefix the handler may return. -/
noncomputable def clockBounds (r : ℕ) (input : RunInput) : ClockBounds :=
  let initial := initialState r input
  ⟨(roundOnline r).totalTime initial, lengthBound r initial, (outputOnline r).totalTime input⟩

private theorem time_castProgram {r : ℕ} {Alpha Beta : Type}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    {first second : Alpha → WordOracleComp (Fin r) Beta}
    (witness : NativeOracleProgram r first encIn encOut) (h : first = second) (input : Alpha) :
    (castProgram witness h).time input = witness.time input := by
  subst second
  rfl

/-- The clock of the retained machine includes initialization, one final stopping round,
copies of each reachable state word, and the final output. Its total bounds the run against
every handler. The factors of five and the additive constants are the costs of the actual
preprocessing, bounded iteration and postprocessing constructors. -/
theorem time_artifact (r : ℕ) (input : RunInput) :
    let bounds := clockBounds r input
    let n := rounds (initialState r input)
    (artifact r).time input =
      5 * (5 * (initialCompiler r).time input +
        ((n + 1) * (bounds.roundTime + 10 * bounds.stateBits + 23) + 8 * bounds.stateBits + 17)
        + 9) + bounds.outputTime + 9 := by
  dsimp only
  rw [artifact, time_castProgram, stagedArtifact, time_castProgram,
    NativeOracleProgram.time_postprocess,
    initializedLoop, NativeOracleProgram.time_preprocess, loopArtifact,
    NativeOracleProgram.time_boundedIterationEncodedOn]
  rfl

/-- **Typed semantics of the retained interpreter.** Run the actual finite-control artifact at its
certified upper-bound clock, adapt its Boolean requests and replies through `wordCodec`, and
decode its output word. Against every adaptive shared-state handler whose encoded replies fit the
declared copied prefix, the resulting joint output/final-state law is exactly `Desc.runOracle`.
The retained machine uses its certified total clock. -/
theorem runWith_artifact_eq_runOracle {OracleState : Type} (input : RunInput)
    (handler : Fin input.desc.operations × List ℕ →
      StateT OracleState PMF (List ℕ)) (state : OracleState)
    (hfit : ReplyPrefixFits handler input.fuel input.replyBits) :
    ProbOracleComp.runWith handler
        ((wordCodec input.desc.operations).adapt
          (unaryListDecoder.decode <$>
            (artifact input.desc.operations).machine.runOracle
              ((artifact input.desc.operations).time input) (eRunInput input))) state =
      ProbOracleComp.runWith handler
        (input.desc.runOracle input.fuel input.input) state := by
  rw [OracleCodec.runWith_adapt, ProbOracleComp.runWith_map]
  change PMF.map _
      (ProbOracleComp.runWith _
        ((artifact input.desc.operations).machine.runOracle
          ((artifact input.desc.operations).online.totalTime input) (eRunInput input)) state) = _
  rw [((artifact input.desc.operations).computes input).runOracle
    ((wordCodec input.desc.operations).wordOracle handler) state]
  rw [ProbOracleComp.runWith_map, PMF.map_comp]
  have hdecode :
      (Prod.map unaryListDecoder.decode (id : OracleState → OracleState) ∘
        Prod.map (⇑(encList encUnary)) (id : OracleState → OracleState)) =
          (id : List ℕ × OracleState → List ℕ × OracleState) := by
    funext outputState
    rcases outputState with ⟨output, finalState⟩
    simp only [Function.comp_apply, Prod.map_apply, unaryListDecoder.decode_enc, id_eq]
  rw [hdecode, PMF.map_id]
  have hsource := runWith_eq_runOracle input handler state hfit
  rw [OracleCodec.runWith_adapt] at hsource
  exact hsource

/-! ### Separate concrete resource coordinates -/

/-- Total stored interpreter and supplied input bits. The controller and dispatch tables
belong to the retained interpreter's description, and the supplied descriptor occurs once as
the framed first field of the runtime word. -/
theorem installed_add_input_bits (r : ℕ) (input : RunInput) :
    (artifact r).staticBits + runInputSize input =
      descLen (artifact r).description +
        (2 * suppliedDescSize input + 1 + runParameterSize input) := by
  rw [runInputSize_eq_framed]
  rfl

/-! ### Static-size families -/

/-- Honest family preservation theorem. In particular, polynomial channel and tape counts do not
discharge `hrows`: the exhaustive table contains the explicit exponential factor
`3 ^ tapeCount * 3 ^ channels`. A growing-channel result therefore needs a separate compressed or
wildcard representation, or an independently proved polynomial exhaustive-row schedule. -/
theorem staticBits_polynomiallyBounded_of_schedules (channels : ℕ → ℕ)
    (htapes : PolynomiallyBounded fun n => (artifact (channels n)).tapeCount)
    (htags : PolynomiallyBounded fun n => (artifact (channels n)).stateTagCount)
    (hchannels : PolynomiallyBounded channels)
    (hinitial : PolynomiallyBounded fun n => (artifact (channels n)).initialStateTag)
    (hrows : PolynomiallyBounded fun n =>
      Description.observationRowCount (artifact (channels n)).stateCard
        (artifact (channels n)).tapeCount (channels n))
    (hmaxRow : PolynomiallyBounded fun n => (artifact (channels n)).maxEncodedRowBits) :
    PolynomiallyBounded fun n => (artifact (channels n)).staticBits := by
  apply Description.staticBits_polynomiallyBounded_of_le htapes htags hchannels hinitial hrows
    hmaxRow
  intro n
  simpa [NativeOracleProgram.staticBitsBound,
    NativeOracleProgram.observationRowCount,
    Description.scheduledBitsBound] using
    (artifact (channels n)).staticBits_le_staticBitsBound

end Turing.MultiTapePTM.Universal.NativeInterpreter

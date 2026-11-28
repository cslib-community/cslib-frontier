/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IterateWhile
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Description
public import CslibFrontier.Computability.Machines.Turing.MultiTape.TapeLemmas

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Lex

/-!
# Named native oracle programs

This internal module retains an actual finite-control `MultiTapePTM` for a word-oracle program,
together with a numbering of its states, its first-order description and a componentwise clock. It
is the open-oracle analogue of the internal `Turing.MultiTapeTM.Internal.NativeCompiler`.

A witness certifies time only: `computes` bounds the machine's tidy run by the total of its clock
ledger, and a workspace coordinate is open in #5467.

The clock ledger is split into twelve phases (`OnlinePhase`). Each constructor assigns its own
split from its submachines' ledgers and the combinator overhead. Only the sum is certified, so an
`OnlineAccounting` value is not a per-phase execution certificate, and a zero entry means only that
the constructor charged nothing to that phase. The external handler's own work is never included.

`NativeOracleProgram.staticBits` is the `descLen` of the description of the retained machine,
charged once. Controls inlined by the constructors are part of that description. Compilers,
interpreters and services that a consuming reduction retains separately are not represented by
this witness and must be charged by that reduction, as must any machine that materializes or scans
a description at runtime.

The semantic function in the type is a specification proved by `computes`, and every witness is
assembled from named machine terms.

A witness is a mathematical object, not an executable generator. `Description.ofMachine` lists the
rows of a given machine in increasing order of encoded key and is a computable definition, but only
the deterministic leaves installed by `ofCompiler` carry an explicit transition table
(`NativeCompiler.table`). The composing constructors store the `noncomputable` machines `tidyComp`,
`itePTM` and `iterateWhile`. The field `computes`, `runWith_descriptionRun` and the `descLen`
bounds are therefore statements about the retained machine in the model. An effective,
table-backed generator for the composed machines is not provided; it is tracked in #5467.

## Main definitions

* `Turing.MultiTapePTM.Internal.NativeOracleProgram`: a named open machine and its clock.
* `Turing.MultiTapePTM.Internal.OnlineAccounting`: a clock split into phases.
* `Turing.MultiTapePTM.Internal.ClassifiedCompiler`: a named deterministic compiler with a phase
  classification of its clock.
* `Turing.MultiTapePTM.Internal.Description.ofMachine`: the first-order description of a machine
  under a numbering of its states.
* `Turing.MultiTapePTM.Internal.NativeOracleProgram.description`: the description of a witness.
* `Turing.MultiTapePTM.Internal.NativeOracleProgram.fairBit`: the named one-step sampler.
* `Turing.MultiTapePTM.Internal.NativeOracleProgram.queryTake`: the named fixed-operation
  bounded-prefix query artifact.
* `Turing.MultiTapePTM.Internal.NativeOracleProgram.ofCompiler`, `.preprocess`, `.postprocess`,
  `.finiteDispatch`, `.sequenceCaptured`, `.boundedIterationEncodedOn`: retained construction
  combinators.

## Main results

* `Turing.MultiTapePTM.Internal.NativeOracleProgram.runWith_descriptionRun`: the generated
  description preserves the retained machine's exact law under every stateful oracle handler.
* `Turing.MultiTapePTM.Internal.Description.table_length_ofMachine`: the description has exactly
  one row for every control, input-head symbol, work-head observation and answer-head observation.

## References

The construction-retaining oracle witness is original to this module.
-/

public section

namespace Turing.MultiTapePTM.Internal

open Cslib Cslib.Probability Turing.MultiTapeMachine Turing.MultiTapeTM

/-! ### Explicit finite descriptions -/

namespace Description

open Turing.MultiTapePTM.Universal
open Turing.MultiTapeTM.Internal.NativeCompiler (stateEncodingBound
  stateEncoding_lt_stateEncodingBound)

variable {k r : ℕ} {State : Type} [Fintype State]

/-- The recorded natural state tag as a control of the declared finite state count. -/
private def stateEmbedding (stateEncoding : State ↪ ℕ) :
    State ↪ Fin (stateEncodingBound stateEncoding) :=
  ⟨fun state => ⟨stateEncoding state, stateEncoding_lt_stateEncodingBound stateEncoding state⟩,
    fun _ _ h => stateEncoding.injective (Fin.ext_iff.mp h)⟩

/-- Native controls occupy the non-trap controls of a first-order description. -/
private def controlEmbedding (stateEncoding : State ↪ ℕ) :
    State ↪ Option (Fin (stateEncodingBound stateEncoding)) :=
  (stateEmbedding stateEncoding).trans
    ⟨some, fun _ _ h => Option.some.inj h⟩

/-- Rename a native action into the alphabet and finite control of its description. -/
private def mapAction (stateEncoding : State ↪ ℕ) :
    MultiTapeMachine.Action k Bool State (Fin r) →
      MultiTapeMachine.Action k ℕ (Option (Fin (stateEncodingBound stateEncoding))) (Fin r)
  | .step ordinary querySymbols answerMoves =>
      .step (ordinary.map (controlEmbedding stateEncoding)
        Turing.MultiTapeTM.Universal.eBit)
        (fun operation => (querySymbols operation).map
          Turing.MultiTapeTM.Universal.eBit)
        answerMoves
  | .query operation next =>
      .query operation (controlEmbedding stateEncoding next)

/-- Encode a native Boolean oracle action into first-order syntax. -/
private def action (stateEncoding : State ↪ ℕ) :
    MultiTapeMachine.Action k Bool State (Fin r) → Universal.Act
  | .step ordinary querySymbols answerMoves =>
      .step (Turing.MultiTapeTM.Universal.Act.ofAction
        (ordinary.map stateEncoding Turing.MultiTapeTM.Universal.eBit))
        (List.ofFn fun operation => (querySymbols operation).map
          Turing.MultiTapeTM.Universal.eBit)
        (List.ofFn answerMoves)
  | .query operation next => .query operation.val (stateEncoding next)

private theorem nextControl_map (stateEncoding : State ↪ ℕ) (state : Option State) :
    Universal.nextControl (stateEncodingBound stateEncoding) (state.map stateEncoding) =
      state.map (controlEmbedding stateEncoding) := by
  cases state with
  | none => rfl
  | some state =>
      change Universal.nextControl (stateEncodingBound stateEncoding)
        (some (stateEncoding state)) = some (controlEmbedding stateEncoding state)
      rw [Universal.nextControl_some_of_lt _ _
        (stateEncoding_lt_stateEncodingBound stateEncoding state)]
      rfl

/-- First-order action denotation is exactly native state/symbol renaming. -/
private theorem action_toAction (stateEncoding : State ↪ ℕ)
    (native : MultiTapeMachine.Action k Bool State (Fin r)) :
    (action stateEncoding native).toAction k (stateEncodingBound stateEncoding) r =
      mapAction stateEncoding native := by
  cases native with
  | step ordinary querySymbols answerMoves =>
      cases ordinary
      simp [action, mapAction, Turing.MultiTapeTM.Universal.Act.ofAction,
        Universal.localAction, Turing.Action.map, controlEmbedding, stateEmbedding,
        nextControl_map]
  | query operation next =>
      rw [action, Universal.Act.toAction_query_of_lt _ _ _ _ _ operation.isLt
        (stateEncoding_lt_stateEncodingBound stateEncoding next)]
      rfl

/-- What a native machine reads in one step: its control, the input-head symbol, the symbol under
each work head and the symbol under each answer head. -/
private abbrev Observation (k r : ℕ) (State : Type) : Type :=
  State × Option Bool × (Fin k → Option Bool) × (Fin r → Option Bool)

/-- The table row of one observation: its encoded key, and the encoded transition for each value
of the private coin. -/
private def row (stateEncoding : State ↪ ℕ) (machine : MultiTapePTM k Bool State (Fin r)) :
    Observation k r State → Universal.Key × Universal.Branches
  | (state, input, work, answers) =>
      (Universal.key (stateEncoding state)
          (input.map Turing.MultiTapeTM.Universal.eBit)
          (Option.map Turing.MultiTapeTM.Universal.eBit ∘ work)
          (Option.map Turing.MultiTapeTM.Universal.eBit ∘ answers),
        { falseBranch := action stateEncoding (machine.tr state input work answers false)
          trueBranch := action stateEncoding (machine.tr state input work answers true) })

omit [Fintype State] in
/-- Distinct observations have distinct row keys. -/
private theorem row_key_injective (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) :
    Function.Injective fun observation => (row stateEncoding machine observation).1 := by
  rintro ⟨state, input, work, answers⟩ ⟨state', input', work', answers'⟩ h
  simp only [row, Universal.key, Universal.Key.mk.injEq,
    Turing.MultiTapeTM.Universal.Key.mk.injEq] at h
  rcases h with ⟨⟨hstate, hinput, hwork⟩, hanswers⟩
  have hwork' := (Option.map_injective
    Turing.MultiTapeTM.Universal.eBit.injective).comp_left (List.ofFn_injective hwork)
  have hanswers' := (Option.map_injective
    Turing.MultiTapeTM.Universal.eBit.injective).comp_left (List.ofFn_injective hanswers)
  rw [stateEncoding.injective hstate,
    Option.map_injective Turing.MultiTapeTM.Universal.eBit.injective hinput,
    hwork', hanswers']

/-- Observations ordered by their encoded row keys. -/
@[instance_reducible] private def observationOrder (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) : LinearOrder (Observation k r State) :=
  LinearOrder.lift'
    (fun observation => Universal.eKey (row stateEncoding machine observation).1)
    (Universal.eKey.injective.comp (row_key_injective stateEncoding machine))

/-- The rows of a native machine's description: one for every control, input-head symbol,
work-head observation and answer-head observation, in increasing order of encoded key. -/
def table (stateEncoding : State ↪ ℕ) (machine : MultiTapePTM k Bool State (Fin r)) :
    List (Universal.Key × Universal.Branches) :=
  letI := observationOrder stateEncoding machine
  ((Finset.univ : Finset (Observation k r State)).sort (· ≤ ·)).map (row stateEncoding machine)

/-- The first-order description of a native machine under a numbering of its states. Its controls
are the state tags below `stateEncodingBound`, and its transition table is `table`. -/
abbrev ofMachine (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) : Universal.Desc :=
  { tapes := k
    states := stateEncodingBound stateEncoding
    operations := r
    q₀ := stateEncoding machine.initial
    table := table stateEncoding machine }

/-- Number of rows of `table`: one of three input-head symbols, one of three symbols at each work
head and one of three symbols at each answer head, for every native control. -/
@[expose] def observationRowCount (stateCard tapeCount operationCount : ℕ) : ℕ :=
  stateCard * 3 * 3 ^ tapeCount * 3 ^ operationCount

/-- The table of `ofMachine` has exactly `observationRowCount` rows. -/
theorem table_length_ofMachine (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) :
    (ofMachine stateEncoding machine).table.length =
      observationRowCount (Fintype.card State) k r := by
  simp [table, observationRowCount, Finset.length_sort, Finset.card_univ,
    Fintype.card_prod, Fintype.card_option, Fintype.card_bool, Fintype.card_fin,
    Nat.mul_assoc]

/-- Looking up the key of an observation in the table returns the row of that observation. -/
private theorem find?_table (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) (observation : Observation k r State) :
    (table stateEncoding machine).find?
        (fun entry => entry.1 = (row stateEncoding machine observation).1) =
      some (row stateEncoding machine observation) := by
  have hmem : row stateEncoding machine observation ∈ table stateEncoding machine :=
    List.mem_map.mpr ⟨observation, by simp, rfl⟩
  obtain ⟨entry, hfind⟩ := Option.isSome_iff_exists.mp
    ((List.find?_isSome
      (p := fun entry => decide (entry.1 = (row stateEncoding machine observation).1))).mpr
      ⟨_, hmem, by simp⟩)
  obtain ⟨other, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfind)
  have hkey : (row stateEncoding machine other).1 = (row stateEncoding machine observation).1 := by
    simpa using List.find?_some hfind
  exact row_key_injective stateEncoding machine hkey ▸ hfind

/-- Description lookup and denotation reproduce the renamed native transition. -/
private theorem ofMachine_action (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) (state : State)
    (input : Option Bool) (work : Fin k → Option Bool) (answers : Fin r → Option Bool)
    (coin : Bool) :
    (ofMachine stateEncoding machine).action (some (stateEmbedding stateEncoding state))
      (input.map Turing.MultiTapeTM.Universal.eBit)
      (Option.map Turing.MultiTapeTM.Universal.eBit ∘ work)
      (Option.map Turing.MultiTapeTM.Universal.eBit ∘ answers) coin =
        mapAction stateEncoding (machine.tr state input work answers coin) := by
  simp only [Universal.Desc.action]
  rw [show ((stateEmbedding stateEncoding state : Fin (stateEncodingBound stateEncoding)) : ℕ) =
    stateEncoding state by rfl]
  change (match (table stateEncoding machine).find?
      (fun entry => entry.1 = (row stateEncoding machine (state, input, work, answers)).1) with
    | none => Universal.haltAction k (stateEncodingBound stateEncoding) r
    | some entry => (entry.2.get coin).toAction k (stateEncodingBound stateEncoding) r) =
      mapAction stateEncoding (machine.tr state input work answers coin)
  rw [find?_table stateEncoding machine (state, input, work, answers)]
  cases coin <;> simp [row, action_toAction]

/-- Decode a natural symbol at the native Boolean boundary. Only `0` and `1` occur on simulated
paths; other symbols are mapped to `false` to make the adapter total. -/
def decodeBit (symbol : ℕ) : Bool := symbol = 1

@[simp] private theorem decodeBit_eBit (bit : Bool) :
    decodeBit (Turing.MultiTapeTM.Universal.eBit bit) = bit := by
  cases bit <;> rfl

private theorem decodeBit_map_eBit (word : List Bool) :
    word.map (decodeBit ∘ Turing.MultiTapeTM.Universal.eBit) = word := by
  induction word with
  | nil => rfl
  | cons bit tail ih =>
      simp only [List.map_cons, Function.comp_apply, decodeBit_eBit, ih]

/-- Rename the symbols stored in one communication channel. -/
private def mapChannel (channel : Channel Bool) : Channel ℕ where
  queryBuffer := channel.queryBuffer.map Turing.MultiTapeTM.Universal.eBit
  answer := channel.answer.map Turing.MultiTapeTM.Universal.eBit
  answerPos := channel.answerPos

/-- Rename ordinary tapes, controls and communication words in one native configuration. -/
private def mapConfig (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) :
    Config k ℕ (Option (Fin (stateEncodingBound stateEncoding))) (Fin r)
      (input.map Turing.MultiTapeTM.Universal.eBit) where
  tapes := cfg.tapes.map (controlEmbedding stateEncoding) Turing.MultiTapeTM.Universal.eBit
  channels operation := mapChannel (cfg.channels operation)

@[simp] private theorem mapConfig_inputSymbol (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) :
    (mapConfig stateEncoding cfg).tapes.inputSymbol =
      cfg.tapes.inputSymbol.map Turing.MultiTapeTM.Universal.eBit :=
  Cfg.inputSymbol_map _ _ _

@[simp] private theorem mapConfig_workTapeSymbols (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) (tape : Fin k) :
    (mapConfig stateEncoding cfg).tapes.workTapeSymbols tape =
      (cfg.tapes.workTapeSymbols tape).map Turing.MultiTapeTM.Universal.eBit :=
  rfl

@[simp] private theorem mapChannel_answerSymbol (channel : Channel Bool) :
    (mapChannel channel).answerSymbol =
      channel.answerSymbol.map Turing.MultiTapeTM.Universal.eBit := by
  by_cases h : 0 ≤ channel.answerPos
  · simp only [mapChannel, Channel.answerSymbol, h, ↓reduceIte, List.getElem?_map]
  · simp only [mapChannel, Channel.answerSymbol, h, ↓reduceIte, Option.map_none]

@[simp] private theorem mapConfig_answerSymbols (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) (operation : Fin r) :
    (mapConfig stateEncoding cfg).answerSymbols operation =
      (cfg.answerSymbols operation).map Turing.MultiTapeTM.Universal.eBit :=
  mapChannel_answerSymbol _

/-- Renaming commutes with initial configurations of a machine and its description. -/
private theorem mapConfig_initial (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) (input : List Bool) :
    mapConfig stateEncoding (machine.initialConfig input) =
      (ofMachine stateEncoding machine).toMachine.initialConfig
        (input.map Turing.MultiTapeTM.Universal.eBit) := by
  change mapConfig stateEncoding (machine.initialConfig input) =
    ({ tapes := Cfg.init
        (Fin.ofNat? (stateEncodingBound stateEncoding) (stateEncoding machine.initial))
        (input.map Turing.MultiTapeTM.Universal.eBit) } :
      Config k ℕ (Option (Fin (stateEncodingBound stateEncoding))) (Fin r)
        (input.map Turing.MultiTapeTM.Universal.eBit))
  apply Config.ext
  · change (Cfg.init machine.initial input).map (controlEmbedding stateEncoding)
      Turing.MultiTapeTM.Universal.eBit = _
    rw [Cfg.map_init]
    rw [Fin.ofNat?_eq_some_of_lt _ _
      (stateEncoding_lt_stateEncodingBound stateEncoding machine.initial)]
    rfl
  · rfl

/-- Renaming commutes with a local tape/channel step. -/
private theorem mapConfig_step (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) (ordinary : Turing.Action k Bool State)
    (querySymbols : Fin r → Option Bool) (answerMoves : Fin r → SignType) :
    (mapConfig stateEncoding cfg).step
      (ordinary.map (controlEmbedding stateEncoding) Turing.MultiTapeTM.Universal.eBit)
      (fun operation => (querySymbols operation).map Turing.MultiTapeTM.Universal.eBit)
      answerMoves =
        mapConfig stateEncoding (cfg.step ordinary querySymbols answerMoves) := by
  apply Config.ext
  · exact Turing.Action.apply_map (controlEmbedding stateEncoding)
      Turing.MultiTapeTM.Universal.eBit ordinary cfg.tapes
  · funext operation
    simp only [Config.step, mapConfig, mapChannel, List.map_append]
    cases querySymbols operation <;> rfl

/-- Renaming commutes with installing an arbitrary reply on one channel. -/
private theorem mapConfig_receive (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) (operation : Fin r) (next : State)
    (reply : List Bool) :
    (mapConfig stateEncoding cfg).receive operation (controlEmbedding stateEncoding next)
      (reply.map Turing.MultiTapeTM.Universal.eBit) =
        mapConfig stateEncoding (cfg.receive operation next reply) := by
  apply Config.ext
  · rfl
  · funext other
    by_cases h : other = operation <;> simp [Config.receive, mapConfig, mapChannel, h]

/-- Query adapter used when executing a natural-symbol description against the original Boolean
word handler: it decodes the request and re-encodes the reply. The adapter is part of the
statement of `NativeOracleProgram.runWith_descriptionRun`; no machine is charged for it. -/
@[expose] def encodedQuery (operation : Fin r) (word : List ℕ) :
    ProbOracleComp (fun _ : Fin r × List Bool => List Bool) (List ℕ) :=
  (List.map Turing.MultiTapeTM.Universal.eBit) <$>
    ProbOracleComp.query (operation, word.map decodeBit)

/-- Every bounded run of the generated first-order description simulates the retained Boolean
machine configuration-for-configuration, including queries and private coins. -/
private theorem runConfigFrom_ofMachine (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) {input : List Bool} (fuel : ℕ)
    (cfg : Config k Bool State (Fin r) input) :
    (ofMachine stateEncoding machine).toMachine.runConfigFrom
        (ProbOracleComp.sample (ProbComp.uniform Bool)) encodedQuery fuel
        (mapConfig stateEncoding cfg) =
      mapConfig stateEncoding <$>
        machine.runOracleConfigFrom fuel cfg := by
  unfold MultiTapePTM.runOracleConfigFrom MultiTapePTM.runConfigFrom
  apply MultiTapeMachine.runConfigFrom_map machine
    (ofMachine stateEncoding machine).toMachine
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun operation word => ProbOracleComp.query (operation, word)) encodedQuery
    (mapConfig stateEncoding)
  intro current
  cases hs : current.tapes.state with
  | none =>
      have htarget : (mapConfig stateEncoding current).tapes.state = none := by
        simp [mapConfig, hs, Cfg.map]
      simp only [MultiTapeMachine.runConfigFrom, hs, htarget]
      exact (PFunctor.FreeM.map_pure _ _).symm
  | some state =>
      have htarget : (mapConfig stateEncoding current).tapes.state =
          some (controlEmbedding stateEncoding state) := by
        simp [mapConfig, hs, Cfg.map, controlEmbedding]
      simp only [MultiTapeMachine.runConfigFrom, hs, htarget, mapConfig_inputSymbol,
        bind_map_left, map_bind]
      congr 1 with coin : 1
      have hwork : (mapConfig stateEncoding current).tapes.workTapeSymbols =
          Option.map Turing.MultiTapeTM.Universal.eBit ∘ current.tapes.workTapeSymbols :=
        funext (mapConfig_workTapeSymbols stateEncoding current)
      have hans : (mapConfig stateEncoding current).answerSymbols =
          Option.map Turing.MultiTapeTM.Universal.eBit ∘ current.answerSymbols :=
        funext (mapConfig_answerSymbols stateEncoding current)
      rw [hwork, hans, Turing.MultiTapePTM.Universal.Desc.toMachine_tr,
        show controlEmbedding stateEncoding state =
          some (stateEmbedding stateEncoding state) from rfl,
        ofMachine_action stateEncoding machine state current.tapes.inputSymbol
          current.tapes.workTapeSymbols current.answerSymbols coin]
      cases haction : machine.tr state current.tapes.inputSymbol current.tapes.workTapeSymbols
          current.answerSymbols coin with
      | step ordinary querySymbols answerMoves =>
          simp only [mapAction, map_pure, mapConfig_step]
      | query operation next =>
          have hquery :
              ((mapConfig stateEncoding current).channels operation).queryBuffer.map decodeBit =
                (current.channels operation).queryBuffer := by
            simpa only [mapConfig, mapChannel, List.map_map] using decodeBit_map_eBit _
          simp only [mapAction, encodedQuery, ProbOracleComp.query]
          rw [hquery]
          simp only [bind_map_left, map_bind, map_pure]
          apply bind_congr
          intro reply
          rw [mapConfig_receive]

/-- The run-level simulation remains exact after interpreting both programs with any shared
stateful Boolean-word handler. -/
private theorem runWith_ofMachine {OracleState : Type} (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) {input : List Bool} (fuel : ℕ)
    (cfg : Config k Bool State (Fin r) input)
    (handler : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) :
    ProbOracleComp.runWith handler
        ((ofMachine stateEncoding machine).toMachine.runConfigFrom
          (ProbOracleComp.sample (ProbComp.uniform Bool)) encodedQuery fuel
          (mapConfig stateEncoding cfg)) state =
      (ProbOracleComp.runWith handler (machine.runOracleConfigFrom fuel cfg) state).map
        (Prod.map (mapConfig stateEncoding) id) := by
  rw [runConfigFrom_ofMachine]
  simp only [ProbOracleComp.runWith_map]

end Description

/-! ### Componentwise online accounting -/

/-- The labels under which a constructor files the clock charges of an online native-oracle
execution. -/
inductive OnlinePhase where
  /-- Copy or scan the presented encoded input. -/
  | inputCopy
  /-- Copy or rewind the final emitted output. -/
  | outputCopy
  /-- Parse boundaries and validate a serialized online structure. -/
  | parsing
  /-- Convert between retained encoded representations. -/
  | codec
  /-- Frame, unframe or otherwise marshal an online word. -/
  | marshalling
  /-- Encode, decode or validate an operation or sum tag. -/
  | tags
  /-- Select one of the fixed finite native branches. -/
  | dispatch
  /-- Scan or select an entry from a retained finite table. -/
  | lookup
  /-- Execute the selected deterministic local transition. -/
  | localStep
  /-- Submit a completed request to the external handler. -/
  | queryIssue
  /-- Copy the retained portion of a handler reply. -/
  | replyCopy
  /-- Run the fixed outer loop or controller around the native primitives. -/
  | controller
  deriving DecidableEq

/-- Explicit enumeration of the twelve disjoint online-accounting phases. -/
instance : Fintype OnlinePhase where
  elems := {.inputCopy, .outputCopy, .parsing, .codec, .marshalling, .tags, .dispatch,
    .lookup, .localStep, .queryIssue, .replyCopy, .controller}
  complete phase := by cases phase <;> simp

@[simp] theorem OnlinePhase.univ_eq : (Finset.univ : Finset OnlinePhase) =
    {.inputCopy, .outputCopy, .parsing, .codec, .marshalling, .tags, .dispatch,
      .lookup, .localStep, .queryIssue, .replyCopy, .controller} :=
  by
    ext phase
    cases phase <;> simp

universe u v w

/-- Construction-assigned time coordinates. The containing named witness certifies only their
sum; each constructor assigns the split. The external handler's own work is not included. -/
structure OnlineAccounting (Alpha : Type u) where
  /-- Time charged to one phase on one input. -/
  time : OnlinePhase → Alpha → ℕ

namespace OnlineAccounting

variable {Alpha : Type u} {Gamma : Type v}

/-- The online clock is the sum of the disjoint phase charges. -/
@[expose] def totalTime (accounting : OnlineAccounting Alpha) (input : Alpha) : ℕ :=
  ∑ phase, accounting.time phase input

theorem time_le_totalTime (accounting : OnlineAccounting Alpha) (phase : OnlinePhase)
    (input : Alpha) : accounting.time phase input ≤ accounting.totalTime input := by
  simpa only [totalTime] using
    (Finset.single_le_sum (f := fun current : OnlinePhase => accounting.time current input)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ phase))

/-- Sequential componentwise accounting: each phase's clocks add. -/
@[expose] def seq (first second : OnlineAccounting Alpha) : OnlineAccounting Alpha where
  time := fun phase input => first.time phase input + second.time phase input

theorem totalTime_seq (first second : OnlineAccounting Alpha) (input : Alpha) :
    (first.seq second).totalTime input = first.totalTime input + second.totalTime input := by
  simp [totalTime, seq, Finset.sum_add_distrib]

/-- Select one complete accounting record without evaluating the unselected branch. -/
private def select (condition : Alpha → Prop) [DecidablePred condition]
    (yes no : OnlineAccounting Alpha) : OnlineAccounting Alpha where
  time := fun phase input => if condition input then yes.time phase input else no.time phase input

private theorem totalTime_select (condition : Alpha → Prop) [DecidablePred condition]
    (yes no : OnlineAccounting Alpha) (input : Alpha) :
    (select condition yes no).totalTime input =
      if condition input then yes.totalTime input else no.totalTime input := by
  by_cases h : condition input <;> simp [totalTime, select, h]

/-- Repeat every phase charge an input-indexed number of times. -/
private def scaleBy (count : Alpha → ℕ) (accounting : OnlineAccounting Alpha) :
    OnlineAccounting Alpha where
  time := fun phase input => count input * accounting.time phase input

private theorem totalTime_scaleBy (count : Alpha → ℕ) (accounting : OnlineAccounting Alpha)
    (input : Alpha) :
    (accounting.scaleBy count).totalTime input = count input * accounting.totalTime input := by
  change (∑ phase, count input * accounting.time phase input) =
    count input * ∑ phase, accounting.time phase input
  rw [Finset.mul_sum]

/-- Reindex phase resources along a semantic input map. A machine constructor using this helper
must separately retain a machine that computes that map. -/
@[expose] def reindex (accounting : OnlineAccounting Alpha) (f : Gamma → Alpha) :
    OnlineAccounting Gamma where
  time := fun phase input => accounting.time phase (f input)

theorem totalTime_reindex (accounting : OnlineAccounting Alpha) (f : Gamma → Alpha)
    (input : Gamma) :
    (accounting.reindex f).totalTime input = accounting.totalTime (f input) :=
  rfl

/-- Add an explicit clock overhead to one phase. -/
@[expose] def addTime (phase : OnlinePhase) (overhead : Alpha → ℕ)
    (accounting : OnlineAccounting Alpha) : OnlineAccounting Alpha where
  time := fun current input =>
    accounting.time current input + if current = phase then overhead input else 0

theorem totalTime_addTime (phase : OnlinePhase) (overhead : Alpha → ℕ)
    (accounting : OnlineAccounting Alpha) (input : Alpha) :
    (accounting.addTime phase overhead).totalTime input =
      accounting.totalTime input + overhead input := by
  cases phase <;> simp [totalTime, addTime, Finset.sum_add_distrib]

end OnlineAccounting

/-! ### Resource-classified deterministic phases -/

/-- A named deterministic compiler together with a componentwise classification of its certified
clock. `compiler.table.toTM` is the executed phase, and `time_eq` ties the classified total to the
machine certificate. -/
structure ClassifiedCompiler {Alpha : Type u} {Beta : Type v} (f : Alpha → Beta)
    (encIn : Alpha ↪ List Bool) (encOut : Beta ↪ List Bool) where
  /-- Retained deterministic finite-control machine. -/
  compiler : Turing.MultiTapeTM.Internal.NativeCompiler f encIn encOut
  /-- Componentwise online classification of its execution. -/
  online : OnlineAccounting Alpha
  /-- The classified clock is exactly the compiler certificate's clock. -/
  time_eq : ∀ input, online.totalTime input = compiler.time input

namespace ClassifiedCompiler

variable {Alpha : Type u} {Beta : Type v} {f : Alpha → Beta}
  {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}

/-- Put a named compiler's whole clock in one construction phase. -/
@[expose] noncomputable def inPhase (phase : OnlinePhase)
    (compiler : Turing.MultiTapeTM.Internal.NativeCompiler f encIn encOut) :
    ClassifiedCompiler f encIn encOut where
  compiler := compiler
  online := { time := fun current input => if current = phase then compiler.time input else 0 }
  time_eq := fun input => by
    cases phase <;> simp [OnlineAccounting.totalTime]

/-- Phase-preserving composition of classified compilers. Child phase records are sequenced and
the tidy-composition clock overhead is charged to marshalling. -/
@[expose] noncomputable def comp {Gamma : Type w} {g : Alpha → Beta} {h : Beta → Gamma}
    {encMid : Beta ↪ List Bool} {encFinal : Gamma ↪ List Bool}
    (outer : ClassifiedCompiler h encMid encFinal)
    (inner : ClassifiedCompiler g encIn encMid) :
    ClassifiedCompiler (fun input => h (g input)) encIn encFinal where
  compiler := outer.compiler.comp inner.compiler
  online := (inner.online.seq (outer.online.reindex g)).addTime .marshalling
    fun input => 4 * (encMid (g input)).length + 9
  time_eq := fun input => by
    rw [OnlineAccounting.totalTime_addTime, OnlineAccounting.totalTime_seq,
      OnlineAccounting.totalTime_reindex,
      show (outer.compiler.comp inner.compiler).time input =
        inner.compiler.time input + outer.compiler.time (g input) +
          4 * (encMid (g input)).length + 9 from rfl,
      inner.time_eq, outer.time_eq]
    omega

/-- Phase-preserving standard-pair construction on a common input. The child records retain their
phases, while the framing and composition clock overhead is charged to marshalling. -/
@[expose] noncomputable def pair {Gamma : Type w} {g : Alpha → Gamma}
    {encLeft : Beta ↪ List Bool}
    {encRight : Gamma ↪ List Bool}
    (left : ClassifiedCompiler f encIn encLeft)
    (right : ClassifiedCompiler g encIn encRight) :
    ClassifiedCompiler (fun input => (f input, g input)) encIn (encPair encLeft encRight) where
  compiler := left.compiler.pair right.compiler
  online := (left.online.seq right.online).addTime .marshalling
    fun input => 8 * (encLeft (f input)).length + 17
  time_eq := fun input => by
    rw [OnlineAccounting.totalTime_addTime, OnlineAccounting.totalTime_seq,
      show (left.compiler.pair right.compiler).time input =
        (left.compiler.time input + (4 * (encLeft (f input)).length + 8) +
            4 * (encLeft (f input)).length + 9) + right.compiler.time input from rfl,
      left.time_eq, right.time_eq]
    omega

end ClassifiedCompiler

/-! ### Named programs -/

/-- A named finite-state native machine for one fixed `Fin r` operation type, with a tidy
certificate that fixes its complete stateful-handler semantics within the recorded clock. -/
structure NativeOracleProgram (r : ℕ) {Alpha : Type u} {Beta : Type}
    (program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta)
    (encIn : Alpha ↪ List Bool) (encOut : Beta ↪ List Bool) where
  /-- Number of ordinary work tapes. -/
  tapeCount : ℕ
  /-- Finite control-state type. -/
  State : Type
  /-- The control is explicitly finite. -/
  [stateFintype : Fintype State]
  /-- The actual native machine term. -/
  machine : MultiTapePTM tapeCount Bool State (Fin r)
  /-- State tags used by the exact first-order description. -/
  stateEncoding : State ↪ ℕ
  /-- Componentwise online time accounting. -/
  online : OnlineAccounting Alpha
  /-- Direct clean-phase computation certificate for the named machine. -/
  computes : ∀ input, machine.ComputesTidily (encIn input) (online.totalTime input)
    (encOut <$> program input)

namespace NativeOracleProgram

variable {r : ℕ} {Alpha : Type u} {Beta : Type}
  {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
  {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}

/-- Native online clock, excluding static artifact size and the external handler's work. -/
@[expose] def time (witness : NativeOracleProgram r program encIn encOut) (input : Alpha) : ℕ :=
  witness.online.totalTime input

/-- Lift a retained deterministic compiler to a named oracle artifact with pure semantics. The
machine is `ofDeterministic classified.compiler.table.toTM`: it ignores private coins and all
oracle channels, keeps the compiler's state numbering and uses the classified clock. -/
@[expose] noncomputable def ofCompiler {Alpha : Type u} {Beta : Type} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (classified : ClassifiedCompiler f encIn encOut) :
    NativeOracleProgram r (fun input => pure (f input)) encIn encOut :=
  letI := classified.compiler.stateFintype
  { tapeCount := classified.compiler.tapeCount
    State := classified.compiler.State
    machine := ofDeterministic classified.compiler.table.toTM
    stateEncoding := classified.compiler.stateEncoding
    online := classified.online
    computes := fun input => by
      rw [classified.time_eq]
      simpa only [map_pure] using
        (ComputesTidily.of_deterministic (Operation := Fin r)
          (classified.compiler.computes input)) }

/-! #### State encodings for retained machine combinators -/

/-- Explicit control tags for tidy sequential composition. -/
private def tidyCompStateEncoding {Inner Outer : Type}
    (inner : Inner ↪ ℕ) (outer : Outer ↪ ℕ) :
    ((Inner ⊕ RewindWorkState) ⊕
      (MarkWorkState ⊕ Outer ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState) ↪ ℕ :=
  Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
    (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding inner
      Turing.MultiTapeTM.Internal.NativeCompiler.rewindWorkStateEncoding)
    (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
      (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
        Turing.MultiTapeTM.Internal.NativeCompiler.markWorkStateEncoding
        (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding outer
          Turing.MultiTapeTM.Internal.NativeCompiler.markWorkStateEncoding))
      (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
        Turing.MultiTapeTM.Internal.NativeCompiler.unitStateEncoding
        Turing.MultiTapeTM.Internal.NativeCompiler.rewindWorkStateEncoding))

/-- Explicit control tags for conditional finite dispatch. -/
private def dispatchStateEncoding {Test Yes No : Type}
    (test : Test ↪ ℕ) (yes : Yes ↪ ℕ) (no : No ↪ ℕ) :
    ((Test ⊕ RewindWorkState) ⊕
      Option (Yes ⊕ No) ⊕ Unit ⊕ RewindWorkState) ↪ ℕ :=
  Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
    (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding test
      Turing.MultiTapeTM.Internal.NativeCompiler.rewindWorkStateEncoding)
    (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
      (Turing.MultiTapeTM.Internal.NativeCompiler.optionStateEncoding
        (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding yes no))
      (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
        Turing.MultiTapeTM.Internal.NativeCompiler.unitStateEncoding
        Turing.MultiTapeTM.Internal.NativeCompiler.rewindWorkStateEncoding))

/-- Explicit tags for the deterministic preparation phase of `iterateWhile`. -/
private def iteratePrepareStateEncoding :
    Turing.MultiTapePTM.IterateWhile.PrepareState ↪ ℕ :=
  Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
    (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
      Turing.MultiTapeTM.Internal.NativeCompiler.unitStateEncoding
      Turing.MultiTapeTM.Internal.NativeCompiler.rewindWorkStateEncoding)
    (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
      (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
        Turing.MultiTapeTM.Internal.NativeCompiler.markWorkStateEncoding
        (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
          (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
            (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
              Turing.MultiTapeTM.Internal.NativeCompiler.unitStateEncoding
              Turing.MultiTapeTM.Internal.NativeCompiler.rewindStateEncoding)
            Turing.MultiTapeTM.Internal.NativeCompiler.rewindWorkStateEncoding)
          Turing.MultiTapeTM.Internal.NativeCompiler.markWorkStateEncoding))
      (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
        Turing.MultiTapeTM.Internal.NativeCompiler.unitStateEncoding
        Turing.MultiTapeTM.Internal.NativeCompiler.rewindWorkStateEncoding))

/-- Explicit tags for the deterministic finishing phase of `iterateWhile`. -/
private def iterateFinishStateEncoding :
    Turing.MultiTapePTM.IterateWhile.FinishState ↪ ℕ :=
  Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
    (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
      Turing.MultiTapeTM.Internal.NativeCompiler.markWorkStateEncoding
      (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
        (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
          Turing.MultiTapeTM.Internal.NativeCompiler.unitStateEncoding
          Turing.MultiTapeTM.Internal.NativeCompiler.rewindStateEncoding)
        Turing.MultiTapeTM.Internal.NativeCompiler.markWorkStateEncoding))
    (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
      Turing.MultiTapeTM.Internal.NativeCompiler.unitStateEncoding
      Turing.MultiTapeTM.Internal.NativeCompiler.rewindWorkStateEncoding)

/-- Explicit control tags for the retained bounded-iteration machine. -/
private def iterateStateEncoding {State : Type} (state : State ↪ ℕ) :
    Turing.MultiTapePTM.IterateWhile.MachineState State ↪ ℕ :=
  let round : Turing.MultiTapePTM.IterateWhile.RoundState State ↪ ℕ :=
    Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding iteratePrepareStateEncoding
      (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
        Turing.MultiTapeTM.Internal.NativeCompiler.markWorkStateEncoding
        (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
          (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding state
            Turing.MultiTapeTM.Internal.NativeCompiler.rewindWorkStateEncoding)
          Turing.MultiTapeTM.Internal.NativeCompiler.markWorkStateEncoding))
  Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
    (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
      (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
        Turing.MultiTapeTM.Internal.NativeCompiler.unitStateEncoding
        Turing.MultiTapeTM.Internal.NativeCompiler.rewindStateEncoding)
      Turing.MultiTapeTM.Internal.NativeCompiler.rewindWorkStateEncoding)
    (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
      (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding round
        Turing.MultiTapeTM.Internal.NativeCompiler.unitStateEncoding)
      iterateFinishStateEncoding)

/-! #### Primitive artifacts -/

/-- The fair-bit primitive charges its single output-emitting native step to output copying. -/
@[expose] def fairBitOnline : OnlineAccounting Alpha where
  time
    | .outputCopy, _ => 1
    | _, _ => 0

theorem totalTime_fairBitOnline (input : Alpha) :
    (fairBitOnline (Alpha := Alpha)).totalTime input = 1 := by
  simp [OnlineAccounting.totalTime, fairBitOnline]

/-- A named one-step fair-bit artifact. The machine ignores the presented input. -/
@[expose] noncomputable def fairBit (encIn : Alpha ↪ List Bool) :
    NativeOracleProgram r
      (fun _ : Alpha => ProbOracleComp.sample (ProbComp.uniform Bool)) encIn encBool where
  tapeCount := 0
  State := Unit
  machine := coinMachine
  stateEncoding := Turing.MultiTapeTM.Internal.NativeCompiler.unitStateEncoding
  online := fairBitOnline
  computes := fun input => by
    rw [totalTime_fairBitOnline]
    exact computesTidily_coinMachine (encIn input)

/-- Explicit enumeration of the four native states of the bounded-prefix query primitive. -/
instance : Fintype QueryTakeState where
  elems := {.marker, .bit, .submit, .copyReply}
  complete state := by cases state <;> simp

/-- Explicit tags for the four native states of the bounded-prefix query primitive. -/
@[expose] def queryTakeStateEncoding : QueryTakeState ↪ ℕ :=
  ⟨fun
      | .marker => 0
      | .bit => 1
      | .submit => 2
      | .copyReply => 3,
    by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- Semantic specification of the fixed-operation bounded-prefix artifact. -/
@[expose] def queryTakeProgram (operation : Fin r) (input : List Bool × ℕ) :
    ProbOracleComp (fun _ : Fin r × List Bool => List Bool) (List Bool) :=
  List.take input.2 <$> ProbOracleComp.query (operation, input.1)

/-- The phase split assigned to the clock of `queryTakePTM`: `2 * q.length + 1` to unframing the
request, one step to submitting the query, `limit + 1` to copying the reply prefix and
`2 * q.length + limit + 3` to rewinding the encoded input. Only the sum is proved
(`totalTime_queryTakeOnline` with the certificate of `queryTake`). -/
@[expose] def queryTakeOnline : OnlineAccounting (List Bool × ℕ) where
  time
    | .inputCopy, (q, limit) => 2 * q.length + limit + 3
    | .parsing, (q, _) => 2 * q.length + 1
    | .queryIssue, _ => 1
    | .replyCopy, (_, limit) => limit + 1
    | _, _ => 0

theorem totalTime_queryTakeOnline (input : List Bool × ℕ) :
    queryTakeOnline.totalTime input = 4 * input.1.length + 2 * input.2 + 6 := by
  rcases input with ⟨q, limit⟩
  norm_num [OnlineAccounting.totalTime, queryTakeOnline]
  omega

/-- The named bounded-prefix query artifact for one fixed operation, which is part of the retained
machine term. -/
@[expose] noncomputable def queryTake (operation : Fin r) :
    NativeOracleProgram r (queryTakeProgram operation)
      (encPair encBits encUnary) encBits where
  tapeCount := 0
  State := QueryTakeState ⊕ RewindState
  machine := queryTakePTM operation
  stateEncoding := Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
    queryTakeStateEncoding Turing.MultiTapeTM.Internal.NativeCompiler.rewindStateEncoding
  online := queryTakeOnline
  computes := fun input => by
    rw [totalTime_queryTakeOnline]
    exact computesTidily_queryTakePTM operation input.1 input.2

/-! #### Retained preprocessing and postprocessing -/

/-- Construction-assigned accounting for deterministic preprocessing followed by a named oracle
program: both ledgers phase by phase, with the `tidyComp` overhead charged to marshalling. -/
private def preprocessAccounting {Alpha : Type u} {Middle : Type v} {Output : Type}
    {f : Alpha → Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOutput : Output ↪ List Bool}
    (prepare : ClassifiedCompiler f encIn encMiddle)
    {program : Middle → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Output}
    (source : NativeOracleProgram r program encMiddle encOutput) : OnlineAccounting Alpha :=
  (prepare.online.seq (source.online.reindex f)).addTime .marshalling
    fun input => 4 * prepare.online.totalTime input + 9

private theorem totalTime_preprocessAccounting {Alpha : Type u} {Middle : Type v} {Output : Type}
    {f : Alpha → Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOutput : Output ↪ List Bool}
    (prepare : ClassifiedCompiler f encIn encMiddle)
    {program : Middle → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Output}
    (source : NativeOracleProgram r program encMiddle encOutput) (input : Alpha) :
    (preprocessAccounting prepare source).totalTime input =
      5 * prepare.compiler.time input + source.time (f input) + 9 := by
  simp only [preprocessAccounting, OnlineAccounting.totalTime_addTime,
    OnlineAccounting.totalTime_seq, OnlineAccounting.totalTime_reindex, time]
  rw [prepare.time_eq]
  omega

private theorem computes_preprocess {Alpha : Type u} {Middle : Type v} {Output : Type}
    {f : Alpha → Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOutput : Output ↪ List Bool}
    (prepare : ClassifiedCompiler f encIn encMiddle)
    {program : Middle → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Output}
    (source : NativeOracleProgram r program encMiddle encOutput) (input : Alpha) :
    (source.machine.tidyComp
      (ofDeterministic (Oracle := Fin r) prepare.compiler.table.toTM) true).ComputesTidily
        (encIn input) ((preprocessAccounting prepare source).totalTime input)
        (encOutput <$> program (f input)) := by
  rw [totalTime_preprocessAccounting]
  have hprepare := ComputesTidily.of_deterministic (Operation := Fin r)
    (prepare.compiler.computes input)
  have hsource := source.computes (f input)
  simpa only [pure_bind] using hprepare.comp
    (prog₂ := fun _ => encOutput <$> program (f input)) true
    (fun word _ _ _ _ hword => by
      simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hword
      rcases Prod.mk.inj hword with ⟨rfl, rfl⟩
      exact hsource)

/-- Execute a named deterministic word preprocessor and then the named oracle artifact. The
result retains the literal `tidyComp` term and all of its finite controls. -/
noncomputable def preprocess {Alpha : Type u} {Middle : Type v} {Output : Type}
    {f : Alpha → Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOutput : Output ↪ List Bool}
    (prepare : ClassifiedCompiler f encIn encMiddle)
    {program : Middle → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Output}
    (source : NativeOracleProgram r program encMiddle encOutput) :
    NativeOracleProgram r (fun input => program (f input)) encIn encOutput :=
  letI := prepare.compiler.stateFintype
  letI := source.stateFintype
  { tapeCount := max prepare.compiler.tapeCount source.tapeCount + 2
    State := (prepare.compiler.State ⊕ RewindWorkState) ⊕
      (MarkWorkState ⊕ source.State ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState
    machine := source.machine.tidyComp
      (ofDeterministic (Oracle := Fin r) prepare.compiler.table.toTM) true
    stateEncoding := tidyCompStateEncoding prepare.compiler.stateEncoding source.stateEncoding
    online := preprocessAccounting prepare source
    computes := computes_preprocess prepare source }

theorem time_preprocess {Alpha : Type u} {Middle : Type v} {Output : Type}
    {f : Alpha → Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOutput : Output ↪ List Bool}
    (prepare : ClassifiedCompiler f encIn encMiddle)
    {program : Middle → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Output}
    (source : NativeOracleProgram r program encMiddle encOutput) (input : Alpha) :
    (preprocess prepare source).time input =
      5 * prepare.compiler.time input + source.time (f input) + 9 :=
  totalTime_preprocessAccounting prepare source input

/-- Construction-assigned accounting for a named oracle computation followed by a named
deterministic typed postprocessor. `postOnline` bounds the postprocessor's time phase by phase on
the source's supported outputs. -/
private def postprocessAccounting {Alpha : Type u} {Middle : Type}
    {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    (source : NativeOracleProgram r program encIn encMiddle)
    (postOnline : OnlineAccounting Alpha) : OnlineAccounting Alpha :=
  (source.online.seq postOnline).addTime .marshalling fun input => 4 * source.time input + 9

private theorem totalTime_postprocessAccounting {Alpha : Type u} {Middle : Type}
    {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    (source : NativeOracleProgram r program encIn encMiddle)
    (postOnline : OnlineAccounting Alpha) (input : Alpha) :
    (postprocessAccounting source postOnline).totalTime input =
      5 * source.time input + postOnline.totalTime input + 9 := by
  simp only [postprocessAccounting, OnlineAccounting.totalTime_addTime,
    OnlineAccounting.totalTime_seq, time]
  omega

private theorem computes_postprocess {Alpha : Type u} {Middle Beta : Type}
    {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    (source : NativeOracleProgram r program encIn encMiddle)
    {f : Middle → Beta} (post : ClassifiedCompiler f encMiddle encOut)
    (postOnline : OnlineAccounting Alpha)
    (hpost : ∀ input (OracleState : Type)
      (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
      (state : OracleState) (middle : Middle) (state' : OracleState),
      (middle, state') ∈ (ProbOracleComp.runWith oracle (program input) state).support →
      ∀ phase, post.online.time phase middle ≤ postOnline.time phase input)
    (input : Alpha) :
    ((ofDeterministic (Oracle := Fin r) post.compiler.table.toTM).tidyComp
      source.machine true).ComputesTidily
      (encIn input) ((postprocessAccounting source postOnline).totalTime input)
        (encOut <$> (f <$> program input)) := by
  rw [totalTime_postprocessAccounting]
  have hsource := source.computes input
  have hcomp := hsource.comp_encoded encMiddle
      (t₂ := postOnline.totalTime input)
      (prog₂ := fun middle => pure (encOut (f middle))) true
      fun middle OracleState oracle state state' hmiddle => by
    have hdet := ComputesTidily.of_deterministic (Operation := Fin r)
      (post.compiler.computes middle)
    refine hdet.mono ?_
    rw [← post.time_eq]
    exact Finset.sum_le_sum fun phase _ =>
      hpost input OracleState oracle state middle state' hmiddle phase
  simpa only [bind_pure_comp, Functor.map_map, Function.comp_apply, time,
    OnlineAccounting.totalTime] using hcomp

/-- Execute a named oracle artifact and then a named deterministic typed postprocessor. The caller
supplies a phasewise bound on the postprocessor for every supported intermediate result, which the
machine passes on in its encoding `encMiddle`. -/
noncomputable def postprocess {Alpha : Type u} {Middle Beta : Type}
    {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    (source : NativeOracleProgram r program encIn encMiddle)
    {f : Middle → Beta} (post : ClassifiedCompiler f encMiddle encOut)
    (postOnline : OnlineAccounting Alpha)
    (hpost : ∀ input (OracleState : Type)
      (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
      (state : OracleState) (middle : Middle) (state' : OracleState),
      (middle, state') ∈ (ProbOracleComp.runWith oracle (program input) state).support →
      ∀ phase, post.online.time phase middle ≤ postOnline.time phase input) :
    NativeOracleProgram r (fun input => f <$> program input) encIn encOut :=
  letI := source.stateFintype
  letI := post.compiler.stateFintype
  { tapeCount := max source.tapeCount post.compiler.tapeCount + 2
    State := (source.State ⊕ RewindWorkState) ⊕
      (MarkWorkState ⊕ post.compiler.State ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState
    machine := (ofDeterministic (Oracle := Fin r) post.compiler.table.toTM).tidyComp
      source.machine true
    stateEncoding := tidyCompStateEncoding source.stateEncoding post.compiler.stateEncoding
    online := postprocessAccounting source postOnline
    computes := computes_postprocess source post postOnline hpost }

theorem time_postprocess {Alpha : Type u} {Middle Beta : Type}
    {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    (source : NativeOracleProgram r program encIn encMiddle)
    {f : Middle → Beta} (post : ClassifiedCompiler f encMiddle encOut)
    (postOnline : OnlineAccounting Alpha)
    (hpost : ∀ input (OracleState : Type)
      (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
      (state : OracleState) (middle : Middle) (state' : OracleState),
      (middle, state') ∈ (ProbOracleComp.runWith oracle (program input) state).support →
      ∀ phase, post.online.time phase middle ≤ postOnline.time phase input)
    (input : Alpha) :
    (postprocess source post postOnline hpost).time input =
      5 * source.time input + postOnline.totalTime input + 9 :=
  totalTime_postprocessAccounting source postOnline input

/-! #### Retained finite dispatch -/

/-- Construction-assigned accounting for a retained binary dispatch node. The test compiler and
selected branch are charged phasewise; the fixed `itePTM` scaffolding is charged to dispatch. -/
private def dispatchAccounting {Alpha : Type u} {Beta : Type}
    {test : Alpha → List Bool}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (condition : ClassifiedCompiler test encIn encBits)
    {yesProgram noProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (yes : NativeOracleProgram r yesProgram encIn encOut)
    (no : NativeOracleProgram r noProgram encIn encOut) : OnlineAccounting Alpha :=
  (condition.online.seq
    (OnlineAccounting.select (fun input => test input ≠ []) yes.online no.online)).addTime
      .dispatch fun input => 4 * (test input).length + 6

private theorem totalTime_dispatchAccounting {Alpha : Type u} {Beta : Type}
    {test : Alpha → List Bool}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (condition : ClassifiedCompiler test encIn encBits)
    {yesProgram noProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (yes : NativeOracleProgram r yesProgram encIn encOut)
    (no : NativeOracleProgram r noProgram encIn encOut) (input : Alpha) :
    (dispatchAccounting condition yes no).totalTime input =
      condition.compiler.time input +
        (if test input = [] then no.time input else yes.time input) +
        4 * (test input).length + 6 := by
  simp only [dispatchAccounting, OnlineAccounting.totalTime_addTime,
    OnlineAccounting.totalTime_seq, OnlineAccounting.totalTime_select, time]
  rw [condition.time_eq]
  by_cases h : test input = [] <;> simp [h, Nat.add_assoc]

private theorem computes_dispatch {Alpha : Type u} {Beta : Type}
    {test : Alpha → List Bool}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (condition : ClassifiedCompiler test encIn encBits)
    {yesProgram noProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (yes : NativeOracleProgram r yesProgram encIn encOut)
    (no : NativeOracleProgram r noProgram encIn encOut) (input : Alpha) :
    (itePTM (ofDeterministic (Oracle := Fin r) condition.compiler.table.toTM)
      yes.machine no.machine).ComputesTidily
        (encIn input) ((dispatchAccounting condition yes no).totalTime input)
        (encOut <$> if test input = [] then noProgram input else yesProgram input) := by
  rw [totalTime_dispatchAccounting]
  have hcondition := ComputesTidily.of_deterministic (Operation := Fin r)
    (condition.compiler.computes input)
  have hbranch := hcondition.ite
    (fun _ => yes.computes input) (fun _ => no.computes input)
  rw [show encOut <$> (if test input = [] then noProgram input else yesProgram input) =
      if test input = [] then encOut <$> noProgram input else encOut <$> yesProgram input by
    split <;> rfl]
  convert hbranch using 1 <;> simp only [time, encBits_apply] <;> rfl

/-- Branch on the nonemptiness of a word produced by a named compiler; only the selected native
branch is executed. This is the binary node of `finiteDispatch`. -/
noncomputable def dispatch {Alpha : Type u} {Beta : Type}
    {test : Alpha → List Bool}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (condition : ClassifiedCompiler test encIn encBits)
    {yesProgram noProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (yes : NativeOracleProgram r yesProgram encIn encOut)
    (no : NativeOracleProgram r noProgram encIn encOut) :
    NativeOracleProgram r
      (fun input => if test input = [] then noProgram input else yesProgram input)
      encIn encOut :=
  letI := condition.compiler.stateFintype
  letI := yes.stateFintype
  letI := no.stateFintype
  { tapeCount := max condition.compiler.tapeCount (max yes.tapeCount no.tapeCount) + 1
    State := (condition.compiler.State ⊕ RewindWorkState) ⊕
      Option (yes.State ⊕ no.State) ⊕ Unit ⊕ RewindWorkState
    machine := itePTM
      (ofDeterministic (Oracle := Fin r) condition.compiler.table.toTM) yes.machine no.machine
    stateEncoding := dispatchStateEncoding condition.compiler.stateEncoding
      yes.stateEncoding no.stateEncoding
    online := dispatchAccounting condition yes no
    computes := computes_dispatch condition yes no }

theorem time_dispatch {Alpha : Type u} {Beta : Type} {test : Alpha → List Bool}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (condition : ClassifiedCompiler test encIn encBits)
    {yesProgram noProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (yes : NativeOracleProgram r yesProgram encIn encOut)
    (no : NativeOracleProgram r noProgram encIn encOut) (input : Alpha) :
    (dispatch condition yes no).time input =
      condition.compiler.time input +
        (if test input = [] then no.time input else yes.time input) +
        4 * (test input).length + 6 :=
  totalTime_dispatchAccounting condition yes no input

/-- One case in a finite retained dispatcher. Both the test and branch are named artifacts. -/
structure DispatchCase (r : ℕ) (Alpha : Type u) (Beta : Type)
    (encIn : Alpha ↪ List Bool)
    (encOut : Beta ↪ List Bool) where
  /-- Word test; nonempty selects this case. -/
  test : Alpha → List Bool
  /-- Actual compiler for the test. -/
  condition : ClassifiedCompiler test encIn encBits
  /-- Selected branch semantics. -/
  program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta
  /-- Actual selected branch artifact. -/
  branch : NativeOracleProgram r program encIn encOut

/-- First-matching-case semantics for a finite list of retained tests and branches. -/
@[expose] def dispatchProgram {Alpha : Type u} {Beta : Type} {encIn : Alpha ↪ List Bool}
    {encOut : Beta ↪ List Bool} (cases : List (DispatchCase r Alpha Beta encIn encOut))
    (fallback : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta) :
    Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta :=
  fun input => match cases with
    | [] => fallback input
    | head :: tail =>
        if head.test input = [] then dispatchProgram tail fallback input else head.program input

/-- Fold finitely many named tests into nested `dispatch` nodes. The resulting machine contains
the controls of every test and every branch. -/
@[expose] noncomputable def finiteDispatch {Alpha : Type u} {Beta : Type}
    {encIn : Alpha ↪ List Bool}
    {encOut : Beta ↪ List Bool} (cases : List (DispatchCase r Alpha Beta encIn encOut))
    {fallbackProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (fallback : NativeOracleProgram r fallbackProgram encIn encOut) :
    NativeOracleProgram r (dispatchProgram cases fallbackProgram) encIn encOut :=
  match cases with
  | [] => fallback
  | head :: tail => dispatch head.condition head.branch (finiteDispatch tail fallback)

/-! #### Sequencing with captured input -/

/-- Stateful semantics of sequencing while retaining the original input for the continuation. -/
@[expose] def capturedProgram {Alpha Middle Beta : Type}
    (first : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle)
    (second : Alpha × Middle →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta)
    (input : Alpha) : ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta := do
  let middle ← first input
  second (input, middle)

/-- Construction-assigned accounting for capturing the input by a framing compiler, appending the
first native result, and running the continuation. -/
private noncomputable def capturedAccounting {Alpha Middle : Type}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {firstProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    (first : NativeOracleProgram r firstProgram encIn encMiddle)
    (secondOnline : OnlineAccounting Alpha) : OnlineAccounting Alpha :=
  (first.online.seq secondOnline).addTime .marshalling fun input =>
    5 * (Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn).time input +
      4 * first.time input + 9

private theorem totalTime_capturedAccounting {Alpha Middle : Type}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {firstProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    (first : NativeOracleProgram r firstProgram encIn encMiddle)
    (secondOnline : OnlineAccounting Alpha) (input : Alpha) :
    (capturedAccounting first secondOnline).totalTime input =
      5 * ((Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn).time input +
        first.time input) +
        secondOnline.totalTime input + 9 := by
  simp only [capturedAccounting, OnlineAccounting.totalTime_addTime,
    OnlineAccounting.totalTime_seq, time]
  omega

private theorem computes_sequenceCaptured {Alpha Middle Beta : Type}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    {firstProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    (first : NativeOracleProgram r firstProgram encIn encMiddle)
    {secondProgram : Alpha × Middle →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (second : NativeOracleProgram r secondProgram (encPair encIn encMiddle) encOut)
    (secondOnline : OnlineAccounting Alpha)
    (hsecond : ∀ input (OracleState : Type)
      (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
      (state : OracleState) (middle : Middle) (state' : OracleState),
      (middle, state') ∈
        (ProbOracleComp.runWith oracle (firstProgram input) state).support →
      ∀ phase, second.online.time phase (input, middle) ≤ secondOnline.time phase input)
    (input : Alpha) :
    (second.machine.tidyComp
      (appendPTM
        (ofDeterministic (Oracle := Fin r)
          (Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn).table.toTM)
        first.machine) true).ComputesTidily
      (encIn input) ((capturedAccounting first secondOnline).totalTime input)
      (encOut <$> capturedProgram firstProgram secondProgram input) := by
  rw [totalTime_capturedAccounting]
  let framing := Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn
  let captureMachine := appendPTM
    (ofDeterministic (Oracle := Fin r) framing.table.toTM) first.machine
  have hcapture := ComputesTidily.prefix (Operation := Fin r) (framing.computes input)
    (first.computes input)
  have hcaptureTyped : captureMachine.ComputesTidily (encIn input)
      (framing.time input + first.time input)
      ((encPair encIn encMiddle) <$>
        ((fun middle => (input, middle)) <$> firstProgram input)) := by
    simpa only [captureMachine, time, encBits_apply, Functor.map_map,
      Function.comp_apply, encPair_apply] using hcapture
  have hcomp := hcaptureTyped.comp_encoded (encPair encIn encMiddle)
      (prog₂ := fun captured => encOut <$> secondProgram captured) true
      fun captured OracleState oracle state state' hcaptured => by
    rw [ProbOracleComp.runWith_map] at hcaptured
    obtain ⟨⟨middle, middleState⟩, hmiddle, heq⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp hcaptured
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    have hcontinuation := second.computes (input, middle)
    have hmono : second.time (input, middle) ≤ secondOnline.totalTime input := by
      change second.online.totalTime (input, middle) ≤ secondOnline.totalTime input
      exact Finset.sum_le_sum fun phase _ =>
        hsecond input OracleState oracle state middle middleState hmiddle phase
    exact hcontinuation.mono hmono
  simpa only [framing, captureMachine, capturedProgram, map_bind, bind_map_left,
    Function.comp_apply] using hcomp

/-- Sequence two named oracle artifacts while retaining the original input. The actual machine
frames the input, appends the encoded first result, then feeds the encoded typed pair to the
continuation. -/
noncomputable def sequenceCaptured {Alpha Middle Beta : Type}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    {firstProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    (first : NativeOracleProgram r firstProgram encIn encMiddle)
    {secondProgram : Alpha × Middle →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (second : NativeOracleProgram r secondProgram (encPair encIn encMiddle) encOut)
    (secondOnline : OnlineAccounting Alpha)
    (hsecond : ∀ input (OracleState : Type)
      (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
      (state : OracleState) (middle : Middle) (state' : OracleState),
      (middle, state') ∈
        (ProbOracleComp.runWith oracle (firstProgram input) state).support →
      ∀ phase, second.online.time phase (input, middle) ≤ secondOnline.time phase input) :
    NativeOracleProgram r (capturedProgram firstProgram secondProgram) encIn encOut :=
  letI framing := Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn
  letI := framing.stateFintype
  letI := first.stateFintype
  letI := second.stateFintype
  { tapeCount := max (max framing.tapeCount first.tapeCount) second.tapeCount + 2
    State := ((framing.State ⊕ first.State) ⊕ RewindWorkState) ⊕
      (MarkWorkState ⊕ second.State ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState
    machine := second.machine.tidyComp
      (appendPTM (ofDeterministic (Oracle := Fin r) framing.table.toTM) first.machine) true
    stateEncoding := tidyCompStateEncoding
      (Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
        framing.stateEncoding first.stateEncoding)
      second.stateEncoding
    online := capturedAccounting first secondOnline
    computes := computes_sequenceCaptured first second secondOnline hsecond }

theorem time_sequenceCaptured {Alpha Middle Beta : Type}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    {firstProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    (first : NativeOracleProgram r firstProgram encIn encMiddle)
    {secondProgram : Alpha × Middle →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (second : NativeOracleProgram r secondProgram (encPair encIn encMiddle) encOut)
    (secondOnline : OnlineAccounting Alpha)
    (hsecond : ∀ input (OracleState : Type)
      (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
      (state : OracleState) (middle : Middle) (state' : OracleState),
      (middle, state') ∈
        (ProbOracleComp.runWith oracle (firstProgram input) state).support →
      ∀ phase, second.online.time phase (input, middle) ≤ secondOnline.time phase input)
    (input : Alpha) :
    (sequenceCaptured first second secondOnline hsecond).time input =
      5 * ((Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn).time input +
        first.time input) + secondOnline.totalTime input + 9 :=
  totalTime_capturedAccounting first secondOnline input

/-! #### Retained bounded iteration -/

/-- Construction-assigned accounting for an input-indexed number of retained native rounds. The
fixed loop machine does not depend on `rounds input`; the schedule only certifies its per-input
stopping point. Each body phase time is charged once per round and once more for the final stopping
round, and the tape-loop scaffolding is charged to the controller. -/
private def boundedIterationAccountingOn
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha) :
    OnlineAccounting Alpha :=
  (roundOnline.scaleBy fun input => rounds input + 1).addTime .controller fun input =>
    (rounds input + 1) * (10 * lengthBound input + 23) + 8 * lengthBound input + 17

private theorem totalTime_boundedIterationAccountingOn
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha)
    (input : Alpha) :
    (boundedIterationAccountingOn rounds lengthBound roundOnline).totalTime input =
      (rounds input + 1) *
          (roundOnline.totalTime input + 10 * lengthBound input + 23) +
        8 * lengthBound input + 17 := by
  simp only [boundedIterationAccountingOn, OnlineAccounting.totalTime_addTime,
    OnlineAccounting.totalTime_scaleBy]
  simp only [Nat.mul_add, Nat.add_assoc]

private theorem computes_boundedIterationEncodedOn
    {Alpha : Type} {enc : Alpha ↪ List Bool} (decoder : Turing.MultiTapeTM.Decoder enc)
    {step : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Alpha}
    (body : NativeOracleProgram r step enc enc)
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha)
    (invariant : Alpha → ℕ → Alpha → Prop)
    (hbase : ∀ initial, invariant initial 0 initial)
    (hclock : ∀ initial n, n ≤ rounds initial → ∀ current, invariant initial n current →
      ∀ phase, body.online.time phase current ≤ roundOnline.time phase initial)
    (hpreserve : ∀ initial n, n < rounds initial → ∀ current,
      invariant initial n current →
      ∀ (OracleState : Type)
        (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
        (state state' : OracleState) (next : Alpha),
        (next, state') ∈ (ProbOracleComp.runWith oracle (step current) state).support →
        invariant initial (n + 1) next ∧ enc next ≠ [])
    (hlast : ∀ initial current, invariant initial (rounds initial) current →
      ∀ (OracleState : Type)
        (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
        (state : OracleState),
        ProbOracleComp.runWith oracle (enc <$> step current) state =
          ProbOracleComp.runWith oracle (pure []) state)
    (hlength : ∀ initial n, n ≤ rounds initial → ∀ current,
      invariant initial n current → (enc current).length ≤ lengthBound initial)
    (input : Alpha) :
    (body.machine.iterateWhile true).ComputesTidily
      (enc input)
      ((boundedIterationAccountingOn rounds lengthBound roundOnline).totalTime input)
      (enc <$> OracleComp.iterate (rounds input) step input) := by
  rw [totalTime_boundedIterationAccountingOn]
  let rawStep : List Bool →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) (List Bool) :=
    fun word => enc <$> step (decoder.decode word)
  let rawInvariant (initial : Alpha) (n : ℕ) (word : List Bool) : Prop :=
    ∃ current, invariant initial n current ∧ word = enc current
  have hloop := ComputesTidily.iterateWhile true (rawInvariant input)
    (show rawInvariant input 0 (enc input) from ⟨input, hbase input, rfl⟩)
    (step := rawStep)
    (fun n hn word hword => by
      obtain ⟨current, hcurrent, rfl⟩ := hword
      have hbody := (body.computes current).mono
        (Finset.sum_le_sum fun phase _ =>
          hclock input n hn.le current hcurrent phase)
      simpa only [rawStep, decoder.decode_enc] using hbody)
    (fun n hn word hword OracleState oracle state state' word' hword' => by
      obtain ⟨current, hcurrent, rfl⟩ := hword
      simp only [rawStep, decoder.decode_enc, ProbOracleComp.runWith_map] at hword'
      obtain ⟨⟨next, nextState⟩, hnext, heq⟩ :=
        (PMF.mem_support_map_iff _ _ _).mp hword'
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      have hnextInvariant := hpreserve input n hn current hcurrent OracleState oracle state
        nextState next hnext
      exact ⟨⟨next, hnextInvariant.1, rfl⟩, hnextInvariant.2⟩)
    (fun word hword => by
      obtain ⟨current, hcurrent, rfl⟩ := hword
      have hbody := (body.computes current).mono
        (Finset.sum_le_sum fun phase _ =>
          hclock input (rounds input) le_rfl current hcurrent phase)
      exact hbody.congr (hlast input current hcurrent))
    (fun n hn word hword => by
      obtain ⟨current, hcurrent, rfl⟩ := hword
      exact hlength input n hn current hcurrent)
  apply hloop.congr
  intro OracleState oracle state
  rw [OracleComp.iterate_map (rounds input) step rawStep enc
    (fun current => by simp only [rawStep, decoder.decode_enc]) input]

/-- Run one fixed named loop machine over typed encoded states under input-indexed round,
encoded-length and phase bounds. The retained machine is `body.machine.iterateWhile true`; the body
machine does all parsing and output encoding, and `decoder` is used only in the proof, to relate
the raw-word loop theorem to reachable encoded states.

The machine and its description are independent of `rounds`, which enters only the certified clock
and the semantics. Normal rounds produce a nonempty encoded next state (`hpreserve`). In the
additional stopping round the body's encoded result is the empty word (`hlast`), which
`iterateWhile` treats as its terminator. -/
noncomputable def boundedIterationEncodedOn
    {Alpha : Type} {enc : Alpha ↪ List Bool} (decoder : Turing.MultiTapeTM.Decoder enc)
    {step : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Alpha}
    (body : NativeOracleProgram r step enc enc)
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha)
    (invariant : Alpha → ℕ → Alpha → Prop)
    (hbase : ∀ initial, invariant initial 0 initial)
    (hclock : ∀ initial n, n ≤ rounds initial → ∀ current, invariant initial n current →
      ∀ phase, body.online.time phase current ≤ roundOnline.time phase initial)
    (hpreserve : ∀ initial n, n < rounds initial → ∀ current,
      invariant initial n current →
      ∀ (OracleState : Type)
        (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
        (state state' : OracleState) (next : Alpha),
        (next, state') ∈ (ProbOracleComp.runWith oracle (step current) state).support →
        invariant initial (n + 1) next ∧ enc next ≠ [])
    (hlast : ∀ initial current, invariant initial (rounds initial) current →
      ∀ (OracleState : Type)
        (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
        (state : OracleState),
        ProbOracleComp.runWith oracle (enc <$> step current) state =
          ProbOracleComp.runWith oracle (pure []) state)
    (hlength : ∀ initial n, n ≤ rounds initial → ∀ current,
      invariant initial n current → (enc current).length ≤ lengthBound initial) :
    NativeOracleProgram r
      (fun input => OracleComp.iterate (rounds input) step input) enc enc :=
  letI := body.stateFintype
  { tapeCount := body.tapeCount + 1 + 2
    State := Turing.MultiTapePTM.IterateWhile.MachineState body.State
    machine := body.machine.iterateWhile true
    stateEncoding := iterateStateEncoding body.stateEncoding
    online := boundedIterationAccountingOn rounds lengthBound roundOnline
    computes := computes_boundedIterationEncodedOn decoder body rounds lengthBound roundOnline
      invariant hbase hclock hpreserve hlast hlength }

/-- Exact clock of typed runtime-indexed iteration, including its final stopping round. -/
theorem time_boundedIterationEncodedOn
    {Alpha : Type} {enc : Alpha ↪ List Bool} (decoder : Turing.MultiTapeTM.Decoder enc)
    {step : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Alpha}
    (body : NativeOracleProgram r step enc enc)
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha)
    (invariant : Alpha → ℕ → Alpha → Prop)
    (hbase hclock hpreserve hlast hlength) (input : Alpha) :
    (boundedIterationEncodedOn decoder body rounds lengthBound roundOnline invariant hbase hclock
      hpreserve hlast hlength).time input =
        (rounds input + 1) *
            (roundOnline.totalTime input + 10 * lengthBound input + 23) +
          8 * lengthBound input + 17 :=
  totalTime_boundedIterationAccountingOn rounds lengthBound roundOnline input

/-- The first-order description of the recorded native machine under its recorded state
numbering. -/
noncomputable abbrev description (witness : NativeOracleProgram r program encIn encOut) :
    Turing.MultiTapePTM.Universal.Desc :=
  letI := witness.stateFintype
  Description.ofMachine witness.stateEncoding witness.machine

/-- Execute the generated natural-symbol description through the explicit Boolean-word query
adapter, retaining its whole clocked output program. -/
@[expose] noncomputable def descriptionRun
    (witness : NativeOracleProgram r program encIn encOut) (input : Alpha) :
    ProbOracleComp (fun _ : Fin r × List Bool => List Bool) (List ℕ) :=
  witness.description.toMachine.runFrom
    (ProbOracleComp.sample (ProbComp.uniform Bool)) Description.encodedQuery
    (witness.time input)
    (witness.description.toMachine.initialConfig
      ((encIn input).map Turing.MultiTapeTM.Universal.eBit))

/-- Run for the recorded clock under any stateful handler, the generated description has the law
of `encOut <$> program input`, joint in the output and the handler's final state, up to the symbol
encoding `eBit`. -/
theorem runWith_descriptionRun (witness : NativeOracleProgram r program encIn encOut)
    {OracleState : Type}
    (handler : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (input : Alpha) (state : OracleState) :
    ProbOracleComp.runWith handler (witness.descriptionRun input) state =
      (ProbOracleComp.runWith handler (encOut <$> program input) state).map
        (Prod.map (List.map Turing.MultiTapeTM.Universal.eBit) id) := by
  let _ := witness.stateFintype
  have hnative := (witness.computes input).runOracle handler state
  rw [MultiTapePTM.runOracle_eq_map] at hnative
  rw [descriptionRun, ← Description.mapConfig_initial, ← hnative]
  simp only [MultiTapePTM.runFrom, ProbOracleComp.runWith_map]
  rw [Description.runWith_ofMachine, PMF.map_comp, PMF.map_comp]
  congr 1

/-- Exact unary-model static length of the named open machine. -/
@[expose] noncomputable def staticBits (witness : NativeOracleProgram r program encIn encOut) : ℕ :=
  Turing.MultiTapePTM.Universal.descLen witness.description

end NativeOracleProgram

end Turing.MultiTapePTM.Internal

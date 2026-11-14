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

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Named native oracle programs

This internal module retains an actual finite-control `MultiTapePTM` for a word-oracle program.
The machine, its explicit state encoding, its exact first-order description, online resource
coordinates and direct semantics remain inspectable construction data. It is the open-oracle
analogue of `Turing.MultiTapeTM.Internal.NativeCompiler`, not a replacement public computability
calculus.

Workspace counts positions visited by ordinary work-tape heads during the recorded clock. Query
buffers, answer words and the external handler's private state are separate communication
resources and are not hidden in finite control. Constructors that copy a reply prefix onto work
storage must therefore charge that storage explicitly.

The online accounting is componentwise bookkeeping: input/output copying, word parsing,
representation codecs, marshalling, operation tags, finite dispatch, table lookup, local steps,
query issue, reply copying and the surrounding controller have separate time and workspace
coordinates. The packaged `computes` and `runsInSpace` fields certify only their aggregate sum and
peak. Each constructor
below fixes its own split from the submachine certificates and exact combinator overhead; an
arbitrary `OnlineAccounting` value is not by itself a per-phase execution certificate. Query issue
and retained reply copying are distinct coordinates; neither includes the external handler's work
or words that remain only in communication channels.

`NativeOracleProgram.staticBits` is exactly the `descLen` of the retained artifact, counted once.
`staticBitsCopies` is only conditional multiplication after a caller supplies a copy count; it
does not discover or certify an installed-artifact inventory. Static bits, online runtime and
emitted output size remain separate coordinates. An offline compiler is represented independently
by `Turing.MultiTapeTM.Internal.NativeCompiler`; its time and workspace are charged only when that
compiler is run. If its emitted result is later installed as code, the consuming construction must
record that separate artifact occurrence. The finite table enumeration in `description` constructs
the stored artifact at the metalevel; it is not a free online whole-code scan. A machine that
materializes or scans a description at runtime must retain that compiler or interpreter and charge
its execution.

The semantic function in the type is a specification proved by `computes`; it is not a callback
available to the machine. This module never extracts a machine from an existential certificate or
uses choice to manufacture construction data.

A zero phase coordinate means that this particular artifact does not execute that phase. It does
not make the work free for a client that does execute it. In particular, the fixed-operation query
artifact has no runtime tag decoder, finite dispatcher or universal interpreter: a concrete
fixed-`r` controller must retain and charge those components itself. This open-machine certificate
charges request construction, submission and retained reply-prefix work, but the external service
implementation remains a separate artifact with its own static, time and workspace certificate.
Likewise, specialization or offline compilation remains outside this witness until its compiler is
actually composed into the executed machine.

## Main definitions

* `Turing.MultiTapePTM.Internal.NativeOracleProgram`: a named open machine and its resources.
* `Turing.MultiTapePTM.Internal.OnlineAccounting`: componentwise native online resources.
* `Turing.MultiTapePTM.Internal.ClassifiedCompiler`: a named deterministic compiler with
  phase-preserving resource classification.
* `Turing.MultiTapePTM.Internal.OpenRunPath`: possible private-coin and arbitrary-reply paths.
* `Turing.MultiTapePTM.Internal.NativeOracleProgram.description`: its first-order description.
* `Turing.MultiTapePTM.Internal.NativeOracleProgram.fairBit`: the named one-step sampler.
* `Turing.MultiTapePTM.Internal.NativeOracleProgram.queryTake`: the named fixed-operation
  bounded-prefix query artifact.
* `Turing.MultiTapePTM.Internal.NativeOracleProgram.encodedOutput`, `.ofCompiler`, `.preprocess`,
  `.postprocess`, `.finiteDispatch`, `.sequenceCaptured`, `.boundedIterationEncodedOn`: retained
  construction combinators.

## Main results

* `Turing.MultiTapePTM.Internal.OpenRunPath.space_le_mul_time_add_one`: the generic clocked
  workspace bound.
* `Turing.MultiTapePTM.Internal.NativeOracleProgram.description_eq_ofMachine`: the exact retained
  description.
* `Turing.MultiTapePTM.Internal.Description.runConfigFrom_ofMachine`: clocked execution of the
  description simulates the retained Boolean machine.
* `Turing.MultiTapePTM.Internal.NativeOracleProgram.postWorkspace_le_postprocess`,
  `.secondWorkspace_le_sequenceCaptured`, `.bodyWorkspace_le_boundedIterationEncodedOn`:
  dynamic subartifact phase workspace remains visible in composed witnesses.

## References

The construction-retaining oracle witness is original to this module.
-/

public section

namespace Turing.MultiTapePTM.Internal

open Cslib Cslib.Probability Turing.MultiTapeMachine Turing.MultiTapeTM

/-! ### Open paths and workspace -/

/-- One possible open-machine step. Private coins range over both bits, and a query may receive an
arbitrary reply word. Communication remains in `Config.channels`; it is not folded into control. -/
def OpenStep {k : ℕ} {State Operation : Type} [DecidableEq Operation]
    (machine : MultiTapePTM k Bool State Operation) (input : List Bool)
    (cfg cfg' : Config k Bool State Operation input) : Prop :=
  match cfg.tapes.state with
  | none => cfg' = cfg
  | some state => ∃ coin, match machine.tr state cfg.tapes.inputSymbol
      cfg.tapes.workTapeSymbols cfg.answerSymbols coin with
    | .step action querySymbols answerMoves =>
        cfg' = cfg.step action querySymbols answerMoves
    | .query operation next => ∃ reply, cfg' = cfg.receive operation next reply

/-- The relation of possible open steps on a fixed input. -/
def openStepRel {k : ℕ} {State Operation : Type} [DecidableEq Operation]
    (machine : MultiTapePTM k Bool State Operation) (input : List Bool) :
    SetRel (Config k Bool State Operation input) (Config k Bool State Operation input) :=
  {(cfg, cfg') | OpenStep machine input cfg cfg'}

/-- A nonempty sequence of open configurations joined by possible coin/reply steps. -/
abbrev OpenRunPath {k : ℕ} {State Operation : Type} [DecidableEq Operation]
    (machine : MultiTapePTM k Bool State Operation) (input : List Bool) :=
  RelSeries (openStepRel machine input)

namespace OpenRunPath

variable {k : ℕ} {State Operation : Type} [DecidableEq Operation]
  {machine : MultiTapePTM k Bool State Operation} {input : List Bool}

/-- Number of machine steps in an open path. -/
def time (path : OpenRunPath machine input) : ℕ := path.length

/-- Positions visited by one ordinary work-tape head. Communication-channel heads are separate. -/
def visitedByTapeHead (path : OpenRunPath machine input) (tape : Fin k) : Finset ℤ :=
  Finset.univ.image fun n => (path n).tapes.workTapePos tape

/-- Number of ordinary cells visited by one work-tape head. -/
def spaceUsedByTape (path : OpenRunPath machine input) (tape : Fin k) : ℕ :=
  (path.visitedByTapeHead tape).card

/-- Total ordinary workspace used by an open path. Query and answer storage is excluded. -/
def space (path : OpenRunPath machine input) : ℕ :=
  ∑ tape, path.spaceUsedByTape tape

/-- Each ordinary head visits at most one cell per configuration. -/
theorem space_le_mul_time_add_one (path : OpenRunPath machine input) :
    path.space ≤ k * (path.time + 1) :=
  calc
    path.space ≤ ∑ _ : Fin k, (path.time + 1) :=
      Finset.sum_le_sum fun _ _ => Finset.card_image_le.trans_eq (Finset.card_fin _)
    _ = k * (path.time + 1) := by simp

end OpenRunPath

/-- Every possible path from the initial configuration within `time` steps uses at most
`workspace` ordinary work-tape cells. -/
def ClockedRunsInSpace {k : ℕ} {State Operation : Type} [DecidableEq Operation]
    (machine : MultiTapePTM k Bool State Operation) (input : List Bool)
    (time workspace : ℕ) : Prop :=
  ∀ path : OpenRunPath machine input,
    path.head = machine.initialConfig input → path.time ≤ time → path.space ≤ workspace

/-- The construction-independent clock-to-workspace bound for open machines. -/
theorem clockedRunsInSpace_mul_time_add_one {k : ℕ} {State Operation : Type}
    [DecidableEq Operation] (machine : MultiTapePTM k Bool State Operation)
    (input : List Bool) (time : ℕ) :
    ClockedRunsInSpace machine input time (k * (time + 1)) := by
  intro path _ htime
  exact path.space_le_mul_time_add_one.trans (Nat.mul_le_mul_left k (Nat.add_le_add_right htime 1))

/-! ### Explicit finite descriptions -/

namespace Description

open Turing.MultiTapePTM.Universal

variable {k r : ℕ} {State : Type} [Fintype State]

/-- One plus the largest explicitly assigned state tag. -/
@[expose] noncomputable def stateCount (stateEncoding : State ↪ ℕ) : ℕ :=
  Finset.univ.sup (fun state => stateEncoding state) + 1

theorem stateEncoding_lt_stateCount (stateEncoding : State ↪ ℕ) (state : State) :
    stateEncoding state < stateCount stateEncoding := by
  unfold stateCount
  exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ state))

/-- The recorded natural state tag as a control of the declared finite state count. -/
@[expose] def stateEmbedding (stateEncoding : State ↪ ℕ) :
    State ↪ Fin (stateCount stateEncoding) :=
  ⟨fun state => ⟨stateEncoding state, stateEncoding_lt_stateCount stateEncoding state⟩,
    fun _ _ h => stateEncoding.injective (Fin.ext_iff.mp h)⟩

/-- Native controls occupy the non-trap controls of a first-order description. -/
@[expose] def controlEmbedding (stateEncoding : State ↪ ℕ) :
    State ↪ Option (Fin (stateCount stateEncoding)) :=
  (stateEmbedding stateEncoding).trans
    ⟨some, fun _ _ h => Option.some.inj h⟩

/-- Rename a native action into the alphabet and finite control of its description. -/
def mapAction (stateEncoding : State ↪ ℕ) :
    MultiTapeMachine.Action k Bool State (Fin r) →
      MultiTapeMachine.Action k ℕ (Option (Fin (stateCount stateEncoding))) (Fin r)
  | .step ordinary querySymbols answerMoves =>
      .step (ordinary.map (controlEmbedding stateEncoding)
        Turing.MultiTapeTM.Universal.eBit)
        (fun operation => (querySymbols operation).map
          Turing.MultiTapeTM.Universal.eBit)
        answerMoves
  | .query operation next =>
      .query operation (controlEmbedding stateEncoding next)

/-- Encode a native Boolean oracle action into first-order syntax. -/
def action (stateEncoding : State ↪ ℕ) :
    MultiTapeMachine.Action k Bool State (Fin r) → Universal.Act
  | .step ordinary querySymbols answerMoves =>
      .step (Turing.MultiTapeTM.Universal.Act.ofAction
        (ordinary.map stateEncoding Turing.MultiTapeTM.Universal.eBit))
        (List.ofFn fun operation => (querySymbols operation).map
          Turing.MultiTapeTM.Universal.eBit)
        (List.ofFn answerMoves)
  | .query operation next => .query operation.val (stateEncoding next)

theorem nextControl_map (stateEncoding : State ↪ ℕ) (state : Option State) :
    Universal.nextControl (stateCount stateEncoding) (state.map stateEncoding) =
      state.map (controlEmbedding stateEncoding) := by
  cases state with
  | none => rfl
  | some state =>
      change Universal.nextControl (stateCount stateEncoding) (some (stateEncoding state)) =
        some (controlEmbedding stateEncoding state)
      rw [Universal.nextControl_some_of_lt _ _
        (stateEncoding_lt_stateCount stateEncoding state)]
      rfl

/-- First-order action denotation is exactly native state/symbol renaming. -/
theorem action_toAction (stateEncoding : State ↪ ℕ)
    (native : MultiTapeMachine.Action k Bool State (Fin r)) :
    (action stateEncoding native).toAction k (stateCount stateEncoding) r =
      mapAction stateEncoding native := by
  cases native with
  | step ordinary querySymbols answerMoves =>
      cases ordinary
      simp [action, mapAction, Turing.MultiTapeTM.Universal.Act.ofAction,
        Universal.localAction, Turing.Action.map, controlEmbedding, stateEmbedding,
        nextControl_map]
  | query operation next =>
      rw [action, Universal.Act.toAction_query_of_lt _ _ _ _ _ operation.isLt
        (stateEncoding_lt_stateCount stateEncoding next)]
      rfl

/-- The two explicitly stored branches of one native transition observation. -/
def branches (stateEncoding : State ↪ ℕ) (machine : MultiTapePTM k Bool State (Fin r))
    (state : State) (input : Option Bool) (work : Fin k → Option Bool)
    (answers : Fin r → Option Bool) : Universal.Branches :=
  { falseBranch := action stateEncoding (machine.tr state input work answers false)
    trueBranch := action stateEncoding (machine.tr state input work answers true) }

omit [Fintype State] in
/-- Encoded transition observations determine the native observation. -/
theorem key_injective (stateEncoding : State ↪ ℕ) : Function.Injective
    (fun entry : State × Option Bool × (Fin k → Option Bool) × (Fin r → Option Bool) =>
      Universal.key (stateEncoding entry.1)
        (entry.2.1.map Turing.MultiTapeTM.Universal.eBit)
        (Option.map Turing.MultiTapeTM.Universal.eBit ∘ entry.2.2.1)
        (Option.map Turing.MultiTapeTM.Universal.eBit ∘ entry.2.2.2)) := by
  rintro ⟨state, input, work, answers⟩ ⟨state', input', work', answers'⟩ h
  simp only [Universal.key, Universal.Key.mk.injEq,
    Turing.MultiTapeTM.Universal.Key.mk.injEq] at h
  rcases h with ⟨⟨hstate, hinput, hwork⟩, hanswers⟩
  have hwork' := (Option.map_injective
    Turing.MultiTapeTM.Universal.eBit.injective).comp_left (List.ofFn_injective hwork)
  have hanswers' := (Option.map_injective
    Turing.MultiTapeTM.Universal.eBit.injective).comp_left (List.ofFn_injective hanswers)
  rw [stateEncoding.injective hstate,
    Option.map_injective Turing.MultiTapeTM.Universal.eBit.injective hinput,
    hwork', hanswers']

/-- Explicitly enumerate every finite control, Boolean read symbol, work-head observation and
finite operation-head observation of a native machine. -/
@[expose] noncomputable def ofMachine (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) : Universal.Desc :=
  { tapes := k
    states := stateCount stateEncoding
    operations := r
    q₀ := stateEncoding machine.initial
    table :=
      (Finset.univ : Finset
        (State × Option Bool × (Fin k → Option Bool) × (Fin r → Option Bool))).toList.map
        fun entry =>
          (Universal.key (stateEncoding entry.1)
            (entry.2.1.map Turing.MultiTapeTM.Universal.eBit)
            (Option.map Turing.MultiTapeTM.Universal.eBit ∘ entry.2.2.1)
            (Option.map Turing.MultiTapeTM.Universal.eBit ∘ entry.2.2.2),
          branches stateEncoding machine entry.1 entry.2.1 entry.2.2.1 entry.2.2.2) }

/-- The explicitly enumerated table selects the native transition at every encoded observation. -/
theorem find?_ofMachine (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) (state : State)
    (input : Option Bool) (work : Fin k → Option Bool) (answers : Fin r → Option Bool) :
    (ofMachine stateEncoding machine).table.find?
      (fun entry => entry.1 = Universal.key (stateEncoding state)
        (input.map Turing.MultiTapeTM.Universal.eBit)
        (Option.map Turing.MultiTapeTM.Universal.eBit ∘ work)
        (Option.map Turing.MultiTapeTM.Universal.eBit ∘ answers)) =
      some (Universal.key (stateEncoding state)
        (input.map Turing.MultiTapeTM.Universal.eBit)
        (Option.map Turing.MultiTapeTM.Universal.eBit ∘ work)
        (Option.map Turing.MultiTapeTM.Universal.eBit ∘ answers),
        branches stateEncoding machine state input work answers) := by
  let target :=
    (Universal.key (stateEncoding state)
      (input.map Turing.MultiTapeTM.Universal.eBit)
      (Option.map Turing.MultiTapeTM.Universal.eBit ∘ work)
      (Option.map Turing.MultiTapeTM.Universal.eBit ∘ answers),
      branches stateEncoding machine state input work answers)
  have hmem : target ∈ (ofMachine stateEncoding machine).table := by
    exact List.mem_map.mpr
      ⟨(state, input, work, answers), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
  obtain ⟨entry, hfind⟩ := Option.isSome_iff_exists.mp
    ((List.find?_isSome (p := fun entry => decide (entry.1 = target.1))).mpr
      ⟨target, hmem, by simp⟩)
  obtain ⟨⟨state', input', work', answers'⟩, -, rfl⟩ :=
    List.mem_map.mp (List.mem_of_find?_eq_some hfind)
  have hkey := List.find?_some hfind
  simp only [decide_eq_true_eq] at hkey
  cases key_injective stateEncoding
    (a₁ := (state', input', work', answers'))
    (a₂ := (state, input, work, answers)) hkey
  exact hfind

/-- Description lookup and denotation reproduce the renamed native transition. -/
theorem ofMachine_action (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) (state : State)
    (input : Option Bool) (work : Fin k → Option Bool) (answers : Fin r → Option Bool)
    (coin : Bool) :
    (ofMachine stateEncoding machine).action (some (stateEmbedding stateEncoding state))
      (input.map Turing.MultiTapeTM.Universal.eBit)
      (Option.map Turing.MultiTapeTM.Universal.eBit ∘ work)
      (Option.map Turing.MultiTapeTM.Universal.eBit ∘ answers) coin =
        mapAction stateEncoding (machine.tr state input work answers coin) := by
  simp only [Universal.Desc.action]
  rw [show ((stateEmbedding stateEncoding state : Fin (stateCount stateEncoding)) : ℕ) =
    stateEncoding state by rfl]
  change (match (ofMachine stateEncoding machine).table.find?
      (fun entry => entry.1 = Universal.key (stateEncoding state)
        (input.map Turing.MultiTapeTM.Universal.eBit)
        (Option.map Turing.MultiTapeTM.Universal.eBit ∘ work)
        (Option.map Turing.MultiTapeTM.Universal.eBit ∘ answers)) with
    | none => Universal.haltAction k (stateCount stateEncoding) r
    | some entry => (entry.2.get coin).toAction k (stateCount stateEncoding) r) =
      mapAction stateEncoding (machine.tr state input work answers coin)
  rw [find?_ofMachine stateEncoding machine state input work answers]
  cases coin <;> simp [branches, action_toAction]

/-- Decode a natural symbol at the native Boolean boundary. Only `0` and `1` occur on simulated
paths; other symbols are mapped to `false` to make the adapter total. -/
def decodeBit (symbol : ℕ) : Bool := symbol = 1

@[simp] theorem decodeBit_eBit (bit : Bool) :
    decodeBit (Turing.MultiTapeTM.Universal.eBit bit) = bit := by
  cases bit <;> rfl

/-- Rename the symbols stored in one communication channel. -/
@[expose] def mapChannel (channel : Channel Bool) : Channel ℕ where
  queryBuffer := channel.queryBuffer.map Turing.MultiTapeTM.Universal.eBit
  answer := channel.answer.map Turing.MultiTapeTM.Universal.eBit
  answerPos := channel.answerPos

/-- Rename ordinary tapes, controls and communication words in one native configuration. -/
@[expose] def mapConfig (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) :
    Config k ℕ (Option (Fin (stateCount stateEncoding))) (Fin r)
      (input.map Turing.MultiTapeTM.Universal.eBit) where
  tapes := cfg.tapes.map (controlEmbedding stateEncoding) Turing.MultiTapeTM.Universal.eBit
  channels operation := mapChannel (cfg.channels operation)

@[simp] theorem mapConfig_inputSymbol (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) :
    (mapConfig stateEncoding cfg).tapes.inputSymbol =
      cfg.tapes.inputSymbol.map Turing.MultiTapeTM.Universal.eBit :=
  Cfg.inputSymbol_map _ _ _

@[simp] theorem mapConfig_workTapeSymbols (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) (tape : Fin k) :
    (mapConfig stateEncoding cfg).tapes.workTapeSymbols tape =
      (cfg.tapes.workTapeSymbols tape).map Turing.MultiTapeTM.Universal.eBit :=
  rfl

@[simp] theorem mapConfig_output (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) :
    (mapConfig stateEncoding cfg).tapes.output =
      cfg.tapes.output.map Turing.MultiTapeTM.Universal.eBit :=
  rfl

@[simp] theorem mapChannel_answerSymbol (channel : Channel Bool) :
    (mapChannel channel).answerSymbol =
      channel.answerSymbol.map Turing.MultiTapeTM.Universal.eBit := by
  by_cases h : 0 ≤ channel.answerPos
  · simp only [mapChannel, Channel.answerSymbol, h, ↓reduceIte, List.getElem?_map]
  · simp only [mapChannel, Channel.answerSymbol, h, ↓reduceIte, Option.map_none]

@[simp] theorem mapConfig_answerSymbols (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) (operation : Fin r) :
    (mapConfig stateEncoding cfg).answerSymbols operation =
      (cfg.answerSymbols operation).map Turing.MultiTapeTM.Universal.eBit :=
  mapChannel_answerSymbol _

/-- Renaming commutes with initial configurations of a machine and its description. -/
theorem mapConfig_initial (stateEncoding : State ↪ ℕ)
    (machine : MultiTapePTM k Bool State (Fin r)) (input : List Bool) :
    mapConfig stateEncoding (machine.initialConfig input) =
      (ofMachine stateEncoding machine).toMachine.initialConfig
        (input.map Turing.MultiTapeTM.Universal.eBit) := by
  change mapConfig stateEncoding (machine.initialConfig input) =
    ({ tapes := Cfg.init
        (Fin.ofNat? (stateCount stateEncoding) (stateEncoding machine.initial))
        (input.map Turing.MultiTapeTM.Universal.eBit) } :
      Config k ℕ (Option (Fin (stateCount stateEncoding))) (Fin r)
        (input.map Turing.MultiTapeTM.Universal.eBit))
  apply Config.ext
  · change (Cfg.init machine.initial input).map (controlEmbedding stateEncoding)
      Turing.MultiTapeTM.Universal.eBit = _
    rw [Cfg.map_init]
    rw [Fin.ofNat?_eq_some_of_lt _ _
      (stateEncoding_lt_stateCount stateEncoding machine.initial)]
    rfl
  · rfl

/-- Renaming commutes with a local tape/channel step. -/
theorem mapConfig_step (stateEncoding : State ↪ ℕ) {input : List Bool}
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
theorem mapConfig_receive (stateEncoding : State ↪ ℕ) {input : List Bool}
    (cfg : Config k Bool State (Fin r) input) (operation : Fin r) (next : State)
    (reply : List Bool) :
    (mapConfig stateEncoding cfg).receive operation (controlEmbedding stateEncoding next)
      (reply.map Turing.MultiTapeTM.Universal.eBit) =
        mapConfig stateEncoding (cfg.receive operation next reply) := by
  apply Config.ext
  · rfl
  · funext other
    by_cases h : other = operation
    · subst other
      simp [Config.receive, mapConfig, mapChannel]
    · simp [Config.receive, mapConfig, mapChannel, h]

@[simp] theorem mapChannel_queryBuffer (channel : Channel Bool) :
    (mapChannel channel).queryBuffer =
      channel.queryBuffer.map Turing.MultiTapeTM.Universal.eBit :=
  rfl

@[simp] theorem decodeBit_map_eBit (word : List Bool) :
    (word.map Turing.MultiTapeTM.Universal.eBit).map decodeBit = word := by
  simp

/-- Query adapter used when executing a natural-symbol description against the original Boolean
word handler. It decodes the request and re-encodes the reply; this work is semantic simulation,
not an uncharged runtime implementation claim. -/
@[expose] def encodedQuery (operation : Fin r) (word : List ℕ) :
    ProbOracleComp (fun _ : Fin r × List Bool => List Bool) (List ℕ) :=
  (List.map Turing.MultiTapeTM.Universal.eBit) <$>
    ProbOracleComp.query (operation, word.map decodeBit)

/-- Every bounded run of the generated first-order description simulates the retained Boolean
machine configuration-for-configuration, including queries and private coins. -/
theorem runConfigFrom_ofMachine (stateEncoding : State ↪ ℕ)
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
      simp [MultiTapeMachine.runConfigFrom, hs, htarget]
  | some state =>
      have htarget : (mapConfig stateEncoding current).tapes.state =
          some (controlEmbedding stateEncoding state) := by
        simp [mapConfig, hs, Cfg.map, controlEmbedding]
      simp only [MultiTapeMachine.runConfigFrom, hs, htarget, mapConfig_inputSymbol,
        mapConfig_workTapeSymbols, mapConfig_answerSymbols, bind_map_left, map_bind]
      congr 1 with coin : 1
      rw [Turing.MultiTapePTM.Universal.Desc.toMachine_tr,
        ofMachine_action stateEncoding machine state current.tapes.inputSymbol
          current.tapes.workTapeSymbols current.answerSymbols coin]
      cases haction : machine.tr state current.tapes.inputSymbol current.tapes.workTapeSymbols
          current.answerSymbols coin with
      | step ordinary querySymbols answerMoves =>
          simp only [mapAction, haction, pure_bind, map_pure]
          exact (mapConfig_step stateEncoding current ordinary querySymbols answerMoves).symm
      | query operation next =>
          simp only [mapAction, haction, encodedQuery, ProbOracleComp.query, map_bind]
          congr 1 with reply : 1
          simpa only [mapConfig_queryBuffer, decodeBit_map_eBit] using
            (mapConfig_receive stateEncoding current operation next reply).symm

/-- The run-level simulation remains exact after interpreting both programs with any shared
stateful Boolean-word handler. -/
theorem runWith_ofMachine {OracleState : Type} (stateEncoding : State ↪ ℕ)
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

/-- Mutually exclusive parts of an online native-oracle execution. These are accounting labels,
not callbacks or additional machine states. -/
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
  deriving DecidableEq, Fintype

/-- Construction-assigned time and ordinary-workspace coordinates. The containing named witness
certifies their aggregate sum and peak; constructor theorems justify the displayed split. Query and
answer words that remain only in communication channels, and the external handler's private work,
are outside `workspace`. -/
structure OnlineAccounting (Alpha : Type) where
  /-- Time charged to one phase on one input. -/
  time : OnlinePhase → Alpha → ℕ
  /-- Ordinary work-tape cells charged to one phase on one input. -/
  workspace : OnlinePhase → Alpha → ℕ

namespace OnlineAccounting

variable {Alpha Gamma : Type}

/-- The online clock is the sum of the disjoint phase charges. -/
@[expose] def totalTime (accounting : OnlineAccounting Alpha) (input : Alpha) : ℕ :=
  ∑ phase, accounting.time phase input

/-- Online ordinary workspace is the peak phase workspace, not the sum of sequential uses. -/
@[expose] def totalWorkspace (accounting : OnlineAccounting Alpha) (input : Alpha) : ℕ :=
  Finset.univ.sup fun phase => accounting.workspace phase input

theorem time_le_totalTime (accounting : OnlineAccounting Alpha) (phase : OnlinePhase)
    (input : Alpha) : accounting.time phase input ≤ accounting.totalTime input := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ phase)

theorem workspace_le_totalWorkspace (accounting : OnlineAccounting Alpha) (phase : OnlinePhase)
    (input : Alpha) : accounting.workspace phase input ≤ accounting.totalWorkspace input :=
  Finset.le_sup (Finset.mem_univ phase)

/-- Sequential componentwise accounting. Each phase's clocks add and its ordinary workspaces take
the peak. Static artifacts and communication storage are deliberately not part of this operation. -/
@[expose] def seq (first second : OnlineAccounting Alpha) : OnlineAccounting Alpha where
  time := fun phase input => first.time phase input + second.time phase input
  workspace := fun phase input => max (first.workspace phase input) (second.workspace phase input)

theorem totalTime_seq (first second : OnlineAccounting Alpha) (input : Alpha) :
    (first.seq second).totalTime input = first.totalTime input + second.totalTime input := by
  simp [totalTime, seq, Finset.sum_add_distrib]

theorem totalWorkspace_seq (first second : OnlineAccounting Alpha) (input : Alpha) :
    (first.seq second).totalWorkspace input =
      max (first.totalWorkspace input) (second.totalWorkspace input) := by
  change (Finset.univ.sup fun phase =>
      max (first.workspace phase input) (second.workspace phase input)) =
    max (Finset.univ.sup fun phase => first.workspace phase input)
      (Finset.univ.sup fun phase => second.workspace phase input)
  apply le_antisymm
  · apply Finset.sup_le
    intro phase _
    exact max_le
      ((Finset.le_sup (Finset.mem_univ phase)).trans (le_max_left _ _))
      ((Finset.le_sup (Finset.mem_univ phase)).trans (le_max_right _ _))
  · apply max_le
    · apply Finset.sup_le
      intro phase _
      exact (le_max_left _ _).trans (Finset.le_sup (Finset.mem_univ phase))
    · apply Finset.sup_le
      intro phase _
      exact (le_max_right _ _).trans (Finset.le_sup (Finset.mem_univ phase))

/-- Select one complete accounting record without evaluating the unselected branch. -/
@[expose] def select (condition : Alpha → Prop) [DecidablePred condition]
    (yes no : OnlineAccounting Alpha) : OnlineAccounting Alpha where
  time := fun phase input => if condition input then yes.time phase input else no.time phase input
  workspace := fun phase input =>
    if condition input then yes.workspace phase input else no.workspace phase input

theorem totalTime_select (condition : Alpha → Prop) [DecidablePred condition]
    (yes no : OnlineAccounting Alpha) (input : Alpha) :
    (select condition yes no).totalTime input =
      if condition input then yes.totalTime input else no.totalTime input := by
  by_cases h : condition input <;> simp [totalTime, select, h]

theorem totalWorkspace_select (condition : Alpha → Prop) [DecidablePred condition]
    (yes no : OnlineAccounting Alpha) (input : Alpha) :
    (select condition yes no).totalWorkspace input =
      if condition input then yes.totalWorkspace input else no.totalWorkspace input := by
  by_cases h : condition input <;> simp [totalWorkspace, select, h]

/-- Repeat every phase charge an input-indexed number of times without changing the phase-local
workspace claim. -/
@[expose] def scaleBy (count : Alpha → ℕ) (accounting : OnlineAccounting Alpha) :
    OnlineAccounting Alpha where
  time := fun phase input => count input * accounting.time phase input
  workspace := accounting.workspace

theorem totalTime_scaleBy (count : Alpha → ℕ) (accounting : OnlineAccounting Alpha)
    (input : Alpha) :
    (accounting.scaleBy count).totalTime input = count input * accounting.totalTime input := by
  simp [totalTime, scaleBy, Finset.mul_sum]

/-- Reindex phase resources along a semantic input map. A machine constructor using this helper
must separately retain a machine that computes that map. -/
@[expose] def reindex (accounting : OnlineAccounting Alpha) (f : Gamma → Alpha) :
    OnlineAccounting Gamma where
  time := fun phase input => accounting.time phase (f input)
  workspace := fun phase input => accounting.workspace phase (f input)

theorem totalTime_reindex (accounting : OnlineAccounting Alpha) (f : Gamma → Alpha)
    (input : Gamma) :
    (accounting.reindex f).totalTime input = accounting.totalTime (f input) :=
  rfl

theorem totalWorkspace_reindex (accounting : OnlineAccounting Alpha) (f : Gamma → Alpha)
    (input : Gamma) :
    (accounting.reindex f).totalWorkspace input = accounting.totalWorkspace (f input) :=
  rfl

/-- Add an explicit clock overhead to one phase. -/
@[expose] def addTime (phase : OnlinePhase) (overhead : Alpha → ℕ)
    (accounting : OnlineAccounting Alpha) : OnlineAccounting Alpha where
  time := fun current input =>
    accounting.time current input + if current = phase then overhead input else 0
  workspace := accounting.workspace

theorem totalTime_addTime (phase : OnlinePhase) (overhead : Alpha → ℕ)
    (accounting : OnlineAccounting Alpha) (input : Alpha) :
    (accounting.addTime phase overhead).totalTime input =
      accounting.totalTime input + overhead input := by
  simp [totalTime, addTime, Finset.sum_add_distrib]

/-- Raise one phase's ordinary-workspace bound to an explicit construction-derived floor. -/
@[expose] def withWorkspaceFloor (phase : OnlinePhase) (bound : Alpha → ℕ)
    (accounting : OnlineAccounting Alpha) : OnlineAccounting Alpha where
  time := accounting.time
  workspace := fun current input =>
    if current = phase then max (accounting.workspace current input) (bound input)
    else accounting.workspace current input

theorem totalTime_withWorkspaceFloor (phase : OnlinePhase) (bound : Alpha → ℕ)
    (accounting : OnlineAccounting Alpha) (input : Alpha) :
    (accounting.withWorkspaceFloor phase bound).totalTime input = accounting.totalTime input :=
  rfl

theorem le_totalWorkspace_withWorkspaceFloor (phase : OnlinePhase) (bound : Alpha → ℕ)
    (accounting : OnlineAccounting Alpha) (input : Alpha) :
    bound input ≤ (accounting.withWorkspaceFloor phase bound).totalWorkspace input := by
  exact (le_max_right _ _).trans
    (Finset.le_sup (f := fun current =>
      if current = phase then max (accounting.workspace current input) (bound input)
      else accounting.workspace current input) (Finset.mem_univ phase))

end OnlineAccounting

/-! ### Resource-classified deterministic phases -/

/-- An actual named deterministic compiler together with a componentwise classification of the
same certified clock and a workspace bound. This adds no semantic callback: `compiler.machine` is
the executed phase, and the equalities tie every aggregate back to its machine certificate. -/
structure ClassifiedCompiler {Alpha Beta : Type} (f : Alpha → Beta)
    (encIn : Alpha ↪ List Bool) (encOut : Beta ↪ List Bool) where
  /-- Retained deterministic finite-control machine. -/
  compiler : Turing.MultiTapeTM.Internal.NativeCompiler f encIn encOut
  /-- Componentwise online classification of its execution. -/
  online : OnlineAccounting Alpha
  /-- The classified clock is exactly the compiler certificate's clock. -/
  time_eq : ∀ input, online.totalTime input = compiler.time input
  /-- The classified peak covers the compiler certificate's ordinary workspace. -/
  workspace_le : ∀ input, compiler.workspace input ≤ online.totalWorkspace input
  /-- The classified peak also covers every open path of the deterministic lift through the
  construction-independent clock bound. -/
  clockWorkspace_le : ∀ input,
    compiler.tapeCount * (compiler.time input + 1) ≤ online.totalWorkspace input

namespace ClassifiedCompiler

variable {Alpha Beta : Type} {f : Alpha → Beta}
  {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}

/-- Raise one construction phase to cover both a named compiler's certified workspace formula and
the construction-independent clock floor, without changing any phase time. -/
@[expose] def finishCompilerAccounting (phase : OnlinePhase)
    (compiler : Turing.MultiTapeTM.Internal.NativeCompiler f encIn encOut)
    (accounting : OnlineAccounting Alpha) : OnlineAccounting Alpha :=
  accounting.withWorkspaceFloor phase fun input =>
    max (compiler.workspace input) (compiler.tapeCount * (compiler.time input + 1))

theorem totalTime_finishCompilerAccounting (phase : OnlinePhase)
    (compiler : Turing.MultiTapeTM.Internal.NativeCompiler f encIn encOut)
    (accounting : OnlineAccounting Alpha) (input : Alpha) :
    (finishCompilerAccounting phase compiler accounting).totalTime input =
      accounting.totalTime input :=
  OnlineAccounting.totalTime_withWorkspaceFloor phase _ accounting input

theorem workspace_le_finishCompilerAccounting (phase : OnlinePhase)
    (compiler : Turing.MultiTapeTM.Internal.NativeCompiler f encIn encOut)
    (accounting : OnlineAccounting Alpha) (input : Alpha) :
    compiler.workspace input ≤
      (finishCompilerAccounting phase compiler accounting).totalWorkspace input :=
  (le_max_left _ _).trans
    (OnlineAccounting.le_totalWorkspace_withWorkspaceFloor phase _ accounting input)

theorem clockWorkspace_le_finishCompilerAccounting (phase : OnlinePhase)
    (compiler : Turing.MultiTapeTM.Internal.NativeCompiler f encIn encOut)
    (accounting : OnlineAccounting Alpha) (input : Alpha) :
    compiler.tapeCount * (compiler.time input + 1) ≤
      (finishCompilerAccounting phase compiler accounting).totalWorkspace input :=
  (le_max_right _ _).trans
    (OnlineAccounting.le_totalWorkspace_withWorkspaceFloor phase _ accounting input)

/-- Package an exact phase-time decomposition for a named compiler, adding only the compiler's
certified workspace formula and generic clock floor to one construction phase. -/
@[expose] def ofAccounting (floorPhase : OnlinePhase)
    (compiler : Turing.MultiTapeTM.Internal.NativeCompiler f encIn encOut)
    (accounting : OnlineAccounting Alpha)
    (htime : ∀ input, accounting.totalTime input = compiler.time input) :
    ClassifiedCompiler f encIn encOut where
  compiler := compiler
  online := finishCompilerAccounting floorPhase compiler accounting
  time_eq := fun input =>
    (totalTime_finishCompilerAccounting floorPhase compiler accounting input).trans (htime input)
  workspace_le := workspace_le_finishCompilerAccounting floorPhase compiler accounting
  clockWorkspace_le := clockWorkspace_le_finishCompilerAccounting floorPhase compiler accounting

/-- Put a named compiler's exact clock and workspace in one construction phase. -/
@[expose] noncomputable def inPhase (phase : OnlinePhase)
    (compiler : Turing.MultiTapeTM.Internal.NativeCompiler f encIn encOut) :
    ClassifiedCompiler f encIn encOut :=
  ofAccounting phase compiler
    { time := fun current input => if current = phase then compiler.time input else 0
      workspace := fun _ _ => 0 }
    fun input => by simp [OnlineAccounting.totalTime]

/-- Phase-preserving composition of classified compilers. Child phase records are sequenced, the
exact tidy-composition clock overhead is charged to marshalling, and only the composed compiler's
workspace formula and generic clock floor are added. -/
@[expose] noncomputable def comp {Gamma : Type} {g : Alpha → Beta} {h : Beta → Gamma}
    {encMid : Beta ↪ List Bool} {encFinal : Gamma ↪ List Bool}
    (outer : ClassifiedCompiler h encMid encFinal)
    (inner : ClassifiedCompiler g encIn encMid) :
    ClassifiedCompiler (fun input => h (g input)) encIn encFinal := by
  let compiler := outer.compiler.comp inner.compiler
  let base := inner.online.seq (outer.online.reindex g)
  apply ofAccounting .marshalling compiler
    (base.addTime .marshalling fun input => 4 * (encMid (g input)).length + 9)
  intro input
  rw [OnlineAccounting.totalTime_addTime, OnlineAccounting.totalTime_seq,
    OnlineAccounting.totalTime_reindex]
  rw [show compiler.time input =
      inner.compiler.time input + outer.compiler.time (g input) +
        4 * (encMid (g input)).length + 9 from rfl,
    inner.time_eq, outer.time_eq]

/-- The phase-preserving composition retains the actual named compiler composition. -/
theorem compiler_comp {Gamma : Type} {g : Alpha → Beta} {h : Beta → Gamma}
    {encMid : Beta ↪ List Bool} {encFinal : Gamma ↪ List Bool}
    (outer : ClassifiedCompiler h encMid encFinal)
    (inner : ClassifiedCompiler g encIn encMid) :
    (outer.comp inner).compiler = outer.compiler.comp inner.compiler :=
  rfl

/-- Phase-preserving standard-pair construction on a common input. The child records retain their
phases, while the exact framing/composition clock overhead is charged to marshalling. -/
@[expose] noncomputable def pair {Gamma : Type} {g : Alpha → Gamma}
    {encLeft : Beta ↪ List Bool}
    {encRight : Gamma ↪ List Bool}
    (left : ClassifiedCompiler f encIn encLeft)
    (right : ClassifiedCompiler g encIn encRight) :
    ClassifiedCompiler (fun input => (f input, g input)) encIn (encPair encLeft encRight) := by
  let compiler := left.compiler.pair right.compiler
  let base := left.online.seq right.online
  apply ofAccounting .marshalling compiler
    (base.addTime .marshalling fun input => 8 * (encLeft (f input)).length + 17)
  intro input
  rw [OnlineAccounting.totalTime_addTime, OnlineAccounting.totalTime_seq]
  rw [show compiler.time input =
      (left.compiler.time input + (4 * (encLeft (f input)).length + 8) +
          4 * (encLeft (f input)).length + 9) + right.compiler.time input from rfl,
    left.time_eq, right.time_eq]
  omega

/-- The phase-preserving pair retains the actual named compiler pair construction. -/
theorem compiler_pair {Gamma : Type} {g : Alpha → Gamma}
    {encLeft : Beta ↪ List Bool}
    {encRight : Gamma ↪ List Bool}
    (left : ClassifiedCompiler f encIn encLeft)
    (right : ClassifiedCompiler g encIn encRight) :
    (left.pair right).compiler = left.compiler.pair right.compiler :=
  rfl

end ClassifiedCompiler

/-! ### Named programs -/

/-- A named finite-state native machine for one fixed `Fin r` operation type. The direct tidy
certificate fixes complete stateful-handler semantics; the path certificate independently records
ordinary workspace for arbitrary replies and private coins. -/
structure NativeOracleProgram (r : ℕ) {Alpha Beta : Type}
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
  /-- Componentwise online time and ordinary-workspace accounting. -/
  online : OnlineAccounting Alpha
  /-- Direct clean-phase computation certificate for the named machine. -/
  computes : ∀ input, machine.ComputesTidily (encIn input) (online.totalTime input)
    (encOut <$> program input)
  /-- Direct workspace certificate over all coins and arbitrary replies. -/
  runsInSpace : ∀ input,
    ClockedRunsInSpace machine (encIn input) (online.totalTime input)
      (online.totalWorkspace input)

namespace NativeOracleProgram

variable {r : ℕ} {Alpha Beta : Type}
  {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
  {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}

/-- Exact length of the input presented to the named online artifact. -/
@[expose] def inputBits (_witness : NativeOracleProgram r program encIn encOut)
    (input : Alpha) : ℕ :=
  (encIn input).length

/-- Exact size of one emitted result. This is indexed by the actual probabilistic result rather
than hidden in the input-indexed clock. -/
@[expose] def outputBits (_witness : NativeOracleProgram r program encIn encOut)
    (output : Beta) : ℕ :=
  (encOut output).length

/-- Native online clock, excluding static artifact size and the external handler's work. -/
@[expose] def time (witness : NativeOracleProgram r program encIn encOut) (input : Alpha) : ℕ :=
  witness.online.totalTime input

/-- Peak ordinary work-tape cells used online. Communication-only storage is excluded. -/
@[expose] def workspace (witness : NativeOracleProgram r program encIn encOut)
    (input : Alpha) : ℕ :=
  witness.online.totalWorkspace input

/-- Reinterpret the already encoded output of a named artifact as a raw word. This executes no
additional phase: the machine, state encoding, componentwise accounting and installed control
table are exactly those of `witness`. -/
@[expose] noncomputable def encodedOutput
    (witness : NativeOracleProgram r program encIn encOut) :
    NativeOracleProgram r (fun input => encOut <$> program input) encIn encBits where
  tapeCount := witness.tapeCount
  State := witness.State
  stateFintype := witness.stateFintype
  machine := witness.machine
  stateEncoding := witness.stateEncoding
  online := witness.online
  computes := fun input => by
    simpa only [encBits_apply, id_map] using witness.computes input
  runsInSpace := witness.runsInSpace

/-- Encoding an artifact's output changes neither its retained machine nor its control table. -/
theorem machine_encodedOutput (witness : NativeOracleProgram r program encIn encOut) :
    witness.encodedOutput.machine = witness.machine :=
  rfl

/-- Encoding an artifact's output is a zero-work reinterpretation of its online accounting. -/
theorem online_encodedOutput (witness : NativeOracleProgram r program encIn encOut) :
    witness.encodedOutput.online = witness.online :=
  rfl

/-- Lift a retained deterministic compiler to a named oracle artifact with pure semantics. The
actual machine is `ofDeterministic classified.compiler.machine`: it ignores private coins and all
oracle channels, retains the compiler state encoding, and uses exactly the classified online
record. No dummy query or semantic callback is introduced. -/
@[expose] noncomputable def ofCompiler {Alpha Beta : Type} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (classified : ClassifiedCompiler f encIn encOut) :
    NativeOracleProgram r (fun input => pure (f input)) encIn encOut := by
  letI := classified.compiler.stateFintype
  exact {
    tapeCount := classified.compiler.tapeCount
    State := classified.compiler.State
    machine := ofDeterministic classified.compiler.machine
    stateEncoding := classified.compiler.stateEncoding
    online := classified.online
    computes := fun input => by
      rw [classified.time_eq]
      simpa only [map_pure] using
        (ComputesTidily.of_deterministic (Operation := Fin r)
          (classified.compiler.computes input))
    runsInSpace := fun input => by
      rw [classified.time_eq]
      intro path hhead htime
      exact (clockedRunsInSpace_mul_time_add_one
        (ofDeterministic (Operation := Fin r) classified.compiler.machine)
        (encIn input) (classified.compiler.time input) path hhead htime).trans
          (classified.clockWorkspace_le input)
  }

/-- The deterministic lift retains the compiler machine through `ofDeterministic`. -/
theorem machine_ofCompiler {Alpha Beta : Type} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (classified : ClassifiedCompiler f encIn encOut) :
    (ofCompiler (r := r) classified).machine = ofDeterministic classified.compiler.machine :=
  rfl

/-- The deterministic lift preserves the classified componentwise accounting exactly. -/
theorem online_ofCompiler {Alpha Beta : Type} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (classified : ClassifiedCompiler f encIn encOut) :
    (ofCompiler (r := r) classified).online = classified.online :=
  rfl

/-! #### State encodings for retained machine combinators -/

/-- Explicit control tags for tidy sequential composition. -/
@[expose] def tidyCompStateEncoding {Inner Outer : Type}
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

/-- Explicit control tags for output concatenation. -/
@[expose] def appendStateEncoding {Left Right : Type}
    (left : Left ↪ ℕ) (right : Right ↪ ℕ) : Left ⊕ Right ↪ ℕ :=
  Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding left right

/-- Explicit control tags for conditional finite dispatch. -/
@[expose] def dispatchStateEncoding {Test Yes No : Type}
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
@[expose] def iteratePrepareStateEncoding :
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
@[expose] def iterateFinishStateEncoding :
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
@[expose] def iterateStateEncoding {State : Type} (state : State ↪ ℕ) :
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

/-! #### Aggregate formulas used by the retained constructors -/

/-- Charge a construction's exact aggregate clock while retaining its phase decomposition, and
put the generic clock-derived workspace certificate in the construction's own phase. -/
@[expose] def finishAccounting (phase : OnlinePhase) (tapes : ℕ)
    (accounting : OnlineAccounting Alpha) : OnlineAccounting Alpha :=
  accounting.withWorkspaceFloor phase fun input =>
    tapes * (accounting.totalTime input + 1)

theorem totalTime_finishAccounting (phase : OnlinePhase) (tapes : ℕ)
    (accounting : OnlineAccounting Alpha) (input : Alpha) :
    (finishAccounting phase tapes accounting).totalTime input = accounting.totalTime input :=
  rfl

theorem clockWorkspace_le_finishAccounting (phase : OnlinePhase) (tapes : ℕ)
    (accounting : OnlineAccounting Alpha) (input : Alpha) :
    tapes * (accounting.totalTime input + 1) ≤
      (finishAccounting phase tapes accounting).totalWorkspace input :=
  OnlineAccounting.le_totalWorkspace_withWorkspaceFloor phase _ accounting input

/-- Adding a construction-wide floor never discards any original phase workspace. -/
theorem workspace_le_finishAccounting (floorPhase : OnlinePhase) (tapes : ℕ)
    (accounting : OnlineAccounting Alpha) (phase : OnlinePhase) (input : Alpha) :
    accounting.workspace phase input ≤
      (finishAccounting floorPhase tapes accounting).totalWorkspace input := by
  refine (show accounting.workspace phase input ≤
      (finishAccounting floorPhase tapes accounting).workspace phase input by
    by_cases hphase : phase = floorPhase
    · simp only [finishAccounting, OnlineAccounting.withWorkspaceFloor, hphase, ↓reduceIte]
      exact le_max_left _ _
    · simp only [finishAccounting, OnlineAccounting.withWorkspaceFloor, hphase, ↓reduceIte]).trans
    (OnlineAccounting.workspace_le_totalWorkspace _ phase input)

/-! #### Primitive artifacts -/

/-- The fair-bit primitive charges its single output-emitting native step to output copying. It has
no separate controller, dispatch or interpreter phase. -/
@[expose] def fairBitOnline : OnlineAccounting Alpha where
  time
    | .outputCopy, _ => 1
    | _, _ => 0
  workspace := fun _ _ => 0

theorem totalTime_fairBitOnline (input : Alpha) :
    (fairBitOnline (Alpha := Alpha)).totalTime input = 1 := by
  simp [OnlineAccounting.totalTime, fairBitOnline]

theorem totalWorkspace_fairBitOnline (input : Alpha) :
    (fairBitOnline (Alpha := Alpha)).totalWorkspace input = 0 := by
  simp [OnlineAccounting.totalWorkspace, fairBitOnline]

/-- A named one-step fair-bit artifact. The presented input is ignored by the actual machine; its
size is still available separately through `inputBits`. -/
@[expose] noncomputable def fairBit (encIn : Alpha ↪ List Bool) :
    NativeOracleProgram r
      (fun _ : Alpha => ProbOracleComp.sample (ProbComp.uniform Bool)) encIn encBool := by
  letI : Fintype Unit := inferInstance
  exact {
    tapeCount := 0
    State := Unit
    machine := coinMachine
    stateEncoding := Turing.MultiTapeTM.Internal.NativeCompiler.unitStateEncoding
    online := fairBitOnline
    computes := fun input => by
      rw [totalTime_fairBitOnline]
      exact computesTidily_coinMachine (encIn input)
    runsInSpace := fun input => by
      rw [totalTime_fairBitOnline, totalWorkspace_fairBitOnline]
      simpa using clockedRunsInSpace_mul_time_add_one
        (coinMachine (Operation := Fin r)) (encIn input) 1
  }

/-- The fair-bit artifact retains the one-state native machine definitionally. -/
theorem machine_fairBit (encIn : Alpha ↪ List Bool) :
    (fairBit (r := r) encIn).machine = coinMachine :=
  rfl

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

/-- Exact phase split of `queryTakePTM`. Request unframing costs `2 * q.length + 1`, submitting
the query costs one step, reply-prefix copying costs `limit + 1`, and rewinding the complete
encoded input costs `2 * q.length + limit + 3`. Channel-resident words use no ordinary workspace. -/
@[expose] def queryTakeOnline : OnlineAccounting (List Bool × ℕ) where
  time
    | .inputCopy, (q, limit) => 2 * q.length + limit + 3
    | .parsing, (q, _) => 2 * q.length + 1
    | .queryIssue, _ => 1
    | .replyCopy, (_, limit) => limit + 1
    | _, _ => 0
  workspace := fun _ _ => 0

theorem totalTime_queryTakeOnline (input : List Bool × ℕ) :
    queryTakeOnline.totalTime input = 4 * input.1.length + 2 * input.2 + 6 := by
  rcases input with ⟨q, limit⟩
  simp only [OnlineAccounting.totalTime, queryTakeOnline] <;> omega

theorem totalWorkspace_queryTakeOnline (input : List Bool × ℕ) :
    queryTakeOnline.totalWorkspace input = 0 := by
  simp [OnlineAccounting.totalWorkspace, queryTakeOnline]

/-- A named fixed-operation bounded-prefix query artifact. The operation is part of the retained
machine term; no operation callback is supplied at runtime. -/
@[expose] noncomputable def queryTake (operation : Fin r) :
    NativeOracleProgram r (queryTakeProgram operation)
      (encPair encBits encUnary) encBits := by
  letI : Fintype QueryTakeState := Fintype.ofFinite QueryTakeState
  letI : Fintype (QueryTakeState ⊕ RewindState) := inferInstance
  exact {
    tapeCount := 0
    State := QueryTakeState ⊕ RewindState
    machine := queryTakePTM operation
    stateEncoding := Turing.MultiTapeTM.Internal.NativeCompiler.sumStateEncoding
      queryTakeStateEncoding Turing.MultiTapeTM.Internal.NativeCompiler.rewindStateEncoding
    online := queryTakeOnline
    computes := fun input => by
      rw [totalTime_queryTakeOnline]
      exact computesTidily_queryTakePTM operation input.1 input.2
    runsInSpace := fun input => by
      rw [totalTime_queryTakeOnline, totalWorkspace_queryTakeOnline]
      simpa using clockedRunsInSpace_mul_time_add_one
        (queryTakePTM operation) (encPair encBits encUnary input)
        (4 * input.1.length + 2 * input.2 + 6)
  }

/-- The fixed-operation artifact retains the bounded-prefix native machine definitionally. -/
theorem machine_queryTake (operation : Fin r) :
    (queryTake operation).machine = queryTakePTM operation :=
  rfl

/-! #### Retained preprocessing and postprocessing -/

/-- Exact construction-assigned accounting for deterministic preprocessing followed by a named
oracle program. The deterministic compiler is executed; it is not a semantic callback. -/
@[expose] def preprocessAccounting {Alpha Middle Output : Type} {f : Alpha → Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOutput : Output ↪ List Bool}
    (prepare : ClassifiedCompiler f encIn encMiddle)
    {program : Middle → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Output}
    (source : NativeOracleProgram r program encMiddle encOutput) : OnlineAccounting Alpha :=
  let tapes := max prepare.compiler.tapeCount source.tapeCount + 2
  let base := prepare.online.seq (source.online.reindex f)
  finishAccounting .marshalling tapes
    (base.addTime .marshalling fun input => 4 * prepare.online.totalTime input + 9)

theorem totalTime_preprocessAccounting {Alpha Middle Output : Type} {f : Alpha → Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOutput : Output ↪ List Bool}
    (prepare : ClassifiedCompiler f encIn encMiddle)
    {program : Middle → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Output}
    (source : NativeOracleProgram r program encMiddle encOutput) (input : Alpha) :
    (preprocessAccounting prepare source).totalTime input =
      5 * prepare.compiler.time input + source.time (f input) + 9 := by
  simp only [preprocessAccounting, totalTime_finishAccounting,
    OnlineAccounting.totalTime_addTime, OnlineAccounting.totalTime_seq]
  rw [prepare.time_eq]
  omega

/-- Execute a named deterministic word preprocessor and then the named oracle artifact. The
result retains the literal `tidyComp` term and all of its finite controls. -/
@[expose] noncomputable def preprocess {Alpha Middle Output : Type} {f : Alpha → Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOutput : Output ↪ List Bool}
    (prepare : ClassifiedCompiler f encIn encMiddle)
    {program : Middle → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Output}
    (source : NativeOracleProgram r program encMiddle encOutput) :
    NativeOracleProgram r (fun input => program (f input)) encIn encOutput := by
  letI := prepare.compiler.stateFintype
  letI := source.stateFintype
  let State :=
    ((prepare.compiler.State ⊕ RewindWorkState) ⊕
      (MarkWorkState ⊕ source.State ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState)
  letI : Fintype State := inferInstance
  let tapes := max prepare.compiler.tapeCount source.tapeCount + 2
  let online := preprocessAccounting prepare source
  let machine := source.machine.tidyComp
    (ofDeterministic (Operation := Fin r) prepare.compiler.machine) true
  exact {
    tapeCount := tapes
    State := State
    machine := machine
    stateEncoding := tidyCompStateEncoding prepare.compiler.stateEncoding source.stateEncoding
    online := online
    computes := fun input => by
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
    runsInSpace := fun input => by
      rw [totalTime_preprocessAccounting]
      intro path hhead htime
      have hspace := clockedRunsInSpace_mul_time_add_one machine (encIn input)
        (5 * prepare.compiler.time input + source.time (f input) + 9) path hhead htime
      refine hspace.trans ?_
      simpa only [online, preprocessAccounting, totalTime_preprocessAccounting] using
        clockWorkspace_le_finishAccounting .marshalling tapes
          ((prepare.online.seq (source.online.reindex f)).addTime .marshalling
            fun input => 4 * prepare.online.totalTime input + 9) input
  }

/-- Preprocessing retains the actual tidy-composition machine definitionally. -/
theorem machine_preprocess {Alpha Middle Output : Type} {f : Alpha → Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOutput : Output ↪ List Bool}
    (prepare : ClassifiedCompiler f encIn encMiddle)
    {program : Middle → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Output}
    (source : NativeOracleProgram r program encMiddle encOutput) :
    (preprocess prepare source).machine = source.machine.tidyComp
      (ofDeterministic prepare.compiler.machine) true :=
  rfl

theorem time_preprocess {Alpha Middle Output : Type} {f : Alpha → Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOutput : Output ↪ List Bool}
    (prepare : ClassifiedCompiler f encIn encMiddle)
    {program : Middle → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Output}
    (source : NativeOracleProgram r program encMiddle encOutput) (input : Alpha) :
    (preprocess prepare source).time input =
      5 * prepare.compiler.time input + source.time (f input) + 9 :=
  totalTime_preprocessAccounting prepare source input

/-- Exact construction-assigned accounting for a named oracle computation followed by a named
deterministic typed postprocessor. `postOnline` bounds the compiler time and workspace phase by
phase on the source's supported outputs. -/
@[expose] def postprocessAccounting {Alpha Middle Beta : Type}
    {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    (source : NativeOracleProgram r program encIn encMiddle)
    {f : Middle → Beta} (post : ClassifiedCompiler f encMiddle encOut)
    (postOnline : OnlineAccounting Alpha) : OnlineAccounting Alpha :=
  let tapes := max source.tapeCount post.compiler.tapeCount + 2
  let base := source.online.seq postOnline
  finishAccounting .marshalling tapes
    (base.addTime .marshalling fun input => 4 * source.time input + 9)

theorem totalTime_postprocessAccounting {Alpha Middle Beta : Type}
    {program : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    (source : NativeOracleProgram r program encIn encMiddle)
    {f : Middle → Beta} (post : ClassifiedCompiler f encMiddle encOut)
    (postOnline : OnlineAccounting Alpha) (input : Alpha) :
    (postprocessAccounting source post postOnline).totalTime input =
      5 * source.time input + postOnline.totalTime input + 9 := by
  simp only [postprocessAccounting, totalTime_finishAccounting,
    OnlineAccounting.totalTime_addTime, OnlineAccounting.totalTime_seq]
  omega

/-- Execute a named oracle artifact and then a named deterministic typed postprocessor. The caller
supplies a phasewise bound on the postprocessor for every supported intermediate result. The
machine passes its encoding directly, avoiding any decoding choice or hidden semantic callback. -/
@[expose] noncomputable def postprocess {Alpha Middle Beta : Type}
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
      ∀ phase,
        post.online.time phase middle ≤ postOnline.time phase input ∧
        post.online.workspace phase middle ≤ postOnline.workspace phase input) :
    NativeOracleProgram r (fun input => f <$> program input) encIn encOut := by
  letI := source.stateFintype
  letI := post.compiler.stateFintype
  let State :=
    ((source.State ⊕ RewindWorkState) ⊕
      (MarkWorkState ⊕ post.compiler.State ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState)
  letI : Fintype State := inferInstance
  let tapes := max source.tapeCount post.compiler.tapeCount + 2
  let online := postprocessAccounting source post postOnline
  let machine := (ofDeterministic (Operation := Fin r) post.compiler.machine).tidyComp
    source.machine true
  exact {
    tapeCount := tapes
    State := State
    machine := machine
    stateEncoding := tidyCompStateEncoding source.stateEncoding post.compiler.stateEncoding
    online := online
    computes := fun input => by
      rw [totalTime_postprocessAccounting]
      have hsource := source.computes input
      have hcomp := hsource.comp_encoded encMiddle
          (prog₂ := fun middle => pure (encOut (f middle))) true
          fun middle OracleState oracle state state' hmiddle => by
        have hdet := ComputesTidily.of_deterministic (Operation := Fin r)
          (post.compiler.computes middle)
        apply hdet.mono
        rw [← post.time_eq]
        exact Finset.sum_le_sum fun phase _ =>
          (hpost input OracleState oracle state middle state' hmiddle phase).1
      simpa only [bind_pure_comp, Functor.map_map, Function.comp_apply] using hcomp
    runsInSpace := fun input => by
      rw [totalTime_postprocessAccounting]
      intro path hhead htime
      have hspace := clockedRunsInSpace_mul_time_add_one machine (encIn input)
        (5 * source.time input + postOnline.totalTime input + 9) path hhead htime
      refine hspace.trans ?_
      simpa only [online, postprocessAccounting, totalTime_postprocessAccounting] using
        clockWorkspace_le_finishAccounting .marshalling tapes
          ((source.online.seq postOnline).addTime .marshalling
            fun input => 4 * source.time input + 9) input
  }

/-- Postprocessing retains the actual tidy-composition machine definitionally. -/
theorem machine_postprocess {Alpha Middle Beta : Type}
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
      ∀ phase,
        post.online.time phase middle ≤ postOnline.time phase input ∧
        post.online.workspace phase middle ≤ postOnline.workspace phase input) :
    (postprocess source post postOnline hpost).machine =
      (ofDeterministic post.compiler.machine).tidyComp source.machine true :=
  rfl

theorem time_postprocess {Alpha Middle Beta : Type}
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
      ∀ phase,
        post.online.time phase middle ≤ postOnline.time phase input ∧
        post.online.workspace phase middle ≤ postOnline.workspace phase input)
    (input : Alpha) :
    (postprocess source post postOnline hpost).time input =
      5 * source.time input + postOnline.totalTime input + 9 :=
  totalTime_postprocessAccounting source post postOnline input

/-- The dynamic postprocessor's claimed phase workspace remains visible in the composed witness. -/
theorem postWorkspace_le_postprocess {Alpha Middle Beta : Type}
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
      ∀ phase,
        post.online.time phase middle ≤ postOnline.time phase input ∧
        post.online.workspace phase middle ≤ postOnline.workspace phase input)
    (input : Alpha) (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (middle : Middle) (state' : OracleState)
    (hmiddle : (middle, state') ∈
      (ProbOracleComp.runWith oracle (program input) state).support)
    (phase : OnlinePhase) :
    post.online.workspace phase middle ≤
      (postprocess source post postOnline hpost).workspace input := by
  change post.online.workspace phase middle ≤
    (postprocessAccounting source post postOnline).totalWorkspace input
  refine (hpost input OracleState oracle state middle state' hmiddle phase).2.trans ?_
  refine (show postOnline.workspace phase input ≤
      ((source.online.seq postOnline).addTime .marshalling
        (fun input => 4 * source.time input + 9)).workspace phase input from
    le_max_right _ _).trans ?_
  exact workspace_le_finishAccounting .marshalling
    (max source.tapeCount post.compiler.tapeCount + 2)
    ((source.online.seq postOnline).addTime .marshalling
      fun input => 4 * source.time input + 9) phase input

/-! #### Retained finite dispatch -/

/-- Exact accounting for a retained binary dispatch node. The test compiler and selected branch
are charged phasewise; the fixed `itePTM` scaffolding is charged to dispatch. -/
@[expose] def dispatchAccounting {Alpha Beta : Type} {test : Alpha → List Bool}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (condition : ClassifiedCompiler test encIn encBits)
    {yesProgram noProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (yes : NativeOracleProgram r yesProgram encIn encOut)
    (no : NativeOracleProgram r noProgram encIn encOut) : OnlineAccounting Alpha :=
  let tapes := max condition.compiler.tapeCount (max yes.tapeCount no.tapeCount) + 1
  let selected := OnlineAccounting.select (fun input => test input ≠ []) yes.online no.online
  let base := condition.online.seq selected
  finishAccounting .dispatch tapes
    (base.addTime .dispatch fun input => 4 * (test input).length + 6)

theorem totalTime_dispatchAccounting {Alpha Beta : Type} {test : Alpha → List Bool}
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
  simp only [dispatchAccounting, totalTime_finishAccounting,
    OnlineAccounting.totalTime_addTime, OnlineAccounting.totalTime_seq,
    OnlineAccounting.totalTime_select]
  rw [condition.time_eq]
  by_cases h : test input = [] <;> simp [h]

/-- Branch on the nonemptiness of a word produced by an actual named compiler. Only the selected
native branch is executed. This is the binary node used by `finiteDispatch`; it performs no
runtime whole-description scan. -/
@[expose] noncomputable def dispatch {Alpha Beta : Type} {test : Alpha → List Bool}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (condition : ClassifiedCompiler test encIn encBits)
    {yesProgram noProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (yes : NativeOracleProgram r yesProgram encIn encOut)
    (no : NativeOracleProgram r noProgram encIn encOut) :
    NativeOracleProgram r
      (fun input => if test input = [] then noProgram input else yesProgram input)
      encIn encOut := by
  letI := condition.compiler.stateFintype
  letI := yes.stateFintype
  letI := no.stateFintype
  let State :=
    ((condition.compiler.State ⊕ RewindWorkState) ⊕
      Option (yes.State ⊕ no.State) ⊕ Unit ⊕ RewindWorkState)
  letI : Fintype State := inferInstance
  let tapes := max condition.compiler.tapeCount (max yes.tapeCount no.tapeCount) + 1
  let online := dispatchAccounting condition yes no
  let machine := itePTM
    (ofDeterministic (Operation := Fin r) condition.compiler.machine) yes.machine no.machine
  exact {
    tapeCount := tapes
    State := State
    machine := machine
    stateEncoding := dispatchStateEncoding condition.compiler.stateEncoding
      yes.stateEncoding no.stateEncoding
    online := online
    computes := fun input => by
      rw [totalTime_dispatchAccounting]
      have hcondition := ComputesTidily.of_deterministic (Operation := Fin r)
        (condition.compiler.computes input)
      have hbranch := hcondition.ite
        (fun _ => yes.computes input) (fun _ => no.computes input)
      by_cases htest : test input = [] <;> simp only [htest, ↓reduceIte] at hbranch ⊢
      · exact hbranch
      · exact hbranch
    runsInSpace := fun input => by
      rw [totalTime_dispatchAccounting]
      intro path hhead htime
      have hspace := clockedRunsInSpace_mul_time_add_one machine (encIn input)
        (condition.compiler.time input +
          (if test input = [] then no.time input else yes.time input) +
          4 * (test input).length + 6) path hhead htime
      refine hspace.trans ?_
      simpa only [online, dispatchAccounting, totalTime_dispatchAccounting] using
        clockWorkspace_le_finishAccounting .dispatch tapes
          ((condition.online.seq
            (OnlineAccounting.select (fun input => test input ≠ []) yes.online no.online)).addTime
              .dispatch fun input => 4 * (test input).length + 6) input
  }

/-- Binary dispatch retains the literal conditional-machine constructor. -/
theorem machine_dispatch {Alpha Beta : Type} {test : Alpha → List Bool}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (condition : ClassifiedCompiler test encIn encBits)
    {yesProgram noProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (yes : NativeOracleProgram r yesProgram encIn encOut)
    (no : NativeOracleProgram r noProgram encIn encOut) :
    (dispatch condition yes no).machine = itePTM
      (ofDeterministic condition.compiler.machine) yes.machine no.machine :=
  rfl

theorem time_dispatch {Alpha Beta : Type} {test : Alpha → List Bool}
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
structure DispatchCase (r : ℕ) (Alpha Beta : Type) (encIn : Alpha ↪ List Bool)
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
@[expose] def dispatchProgram {Alpha Beta : Type} {encIn : Alpha ↪ List Bool}
    {encOut : Beta ↪ List Bool} (cases : List (DispatchCase r Alpha Beta encIn encOut))
    (fallback : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta) :
    Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta :=
  fun input => match cases with
    | [] => fallback input
    | head :: tail =>
        if head.test input = [] then dispatchProgram tail fallback input else head.program input

/-- Fold finitely many named tests into nested retained conditional machines. The resulting
artifact contains every test and branch control table; selection does not invoke a callback. -/
@[expose] noncomputable def finiteDispatch {Alpha Beta : Type} {encIn : Alpha ↪ List Bool}
    {encOut : Beta ↪ List Bool} (cases : List (DispatchCase r Alpha Beta encIn encOut))
    {fallbackProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (fallback : NativeOracleProgram r fallbackProgram encIn encOut) :
    NativeOracleProgram r (dispatchProgram cases fallbackProgram) encIn encOut :=
  match cases with
  | [] => fallback
  | head :: tail => dispatch head.condition head.branch (finiteDispatch tail fallback)

@[simp] theorem machine_finiteDispatch_nil {Alpha Beta : Type} {encIn : Alpha ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    {fallbackProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (fallback : NativeOracleProgram r fallbackProgram encIn encOut) :
    (finiteDispatch [] fallback).machine = fallback.machine :=
  rfl

theorem machine_finiteDispatch_cons {Alpha Beta : Type} {encIn : Alpha ↪ List Bool}
    {encOut : Beta ↪ List Bool} (head : DispatchCase r Alpha Beta encIn encOut)
    (tail : List (DispatchCase r Alpha Beta encIn encOut))
    {fallbackProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (fallback : NativeOracleProgram r fallbackProgram encIn encOut) :
    (finiteDispatch (head :: tail) fallback).machine = itePTM
      (ofDeterministic head.condition.compiler.machine) head.branch.machine
        (finiteDispatch tail fallback).machine :=
  rfl

/-! #### Sequencing with captured input -/

/-- Stateful semantics of sequencing while retaining the original input for the continuation. -/
@[expose] def capturedProgram {Alpha Middle Beta : Type}
    (first : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle)
    (second : Alpha × Middle →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta)
    (input : Alpha) : ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta := do
  let middle ← first input
  second (input, middle)

/-- Exact accounting for capturing the input by an actual framing compiler, appending the first
native result, and running the continuation. -/
@[expose] def capturedAccounting {Alpha Middle Beta : Type}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    {firstProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    (first : NativeOracleProgram r firstProgram encIn encMiddle)
    {secondProgram : Alpha × Middle →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (second : NativeOracleProgram r secondProgram (encPair encIn encMiddle) encOut)
    (secondOnline : OnlineAccounting Alpha) : OnlineAccounting Alpha :=
  let framing := Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn
  let captureTapes := max framing.tapeCount first.tapeCount
  let tapes := max captureTapes second.tapeCount + 2
  let base := first.online.seq secondOnline
  finishAccounting .marshalling tapes
    (base.addTime .marshalling fun input =>
      5 * framing.time input + 4 * first.time input + 9)

theorem totalTime_capturedAccounting {Alpha Middle Beta : Type}
    {encIn : Alpha ↪ List Bool} {encMiddle : Middle ↪ List Bool}
    {encOut : Beta ↪ List Bool}
    {firstProgram : Alpha →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Middle}
    (first : NativeOracleProgram r firstProgram encIn encMiddle)
    {secondProgram : Alpha × Middle →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Beta}
    (second : NativeOracleProgram r secondProgram (encPair encIn encMiddle) encOut)
    (secondOnline : OnlineAccounting Alpha) (input : Alpha) :
    (capturedAccounting first second secondOnline).totalTime input =
      5 * ((Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn).time input +
        first.time input) +
        secondOnline.totalTime input + 9 := by
  simp only [capturedAccounting, totalTime_finishAccounting,
    OnlineAccounting.totalTime_addTime, OnlineAccounting.totalTime_seq]
  omega

/-- Sequence two named oracle artifacts while retaining the original input. The actual machine
frames the input, appends the encoded first result, then feeds the encoded typed pair to the
continuation. -/
@[expose] noncomputable def sequenceCaptured {Alpha Middle Beta : Type}
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
      ∀ phase,
        second.online.time phase (input, middle) ≤ secondOnline.time phase input ∧
        second.online.workspace phase (input, middle) ≤ secondOnline.workspace phase input) :
    NativeOracleProgram r (capturedProgram firstProgram secondProgram) encIn encOut := by
  let framing := Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn
  letI := framing.stateFintype
  letI := first.stateFintype
  letI := second.stateFintype
  let CaptureState := framing.State ⊕ first.State
  let State :=
    ((CaptureState ⊕ RewindWorkState) ⊕
      (MarkWorkState ⊕ second.State ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState)
  letI : Fintype CaptureState := inferInstance
  letI : Fintype State := inferInstance
  let captureTapes := max framing.tapeCount first.tapeCount
  let tapes := max captureTapes second.tapeCount + 2
  let captureMachine := appendPTM
    (ofDeterministic (Operation := Fin r) framing.machine) first.machine
  let machine := second.machine.tidyComp captureMachine true
  let online := capturedAccounting first second secondOnline
  exact {
    tapeCount := tapes
    State := State
    machine := machine
    stateEncoding := tidyCompStateEncoding
      (appendStateEncoding framing.stateEncoding first.stateEncoding) second.stateEncoding
    online := online
    computes := fun input => by
      rw [totalTime_capturedAccounting]
      have hcapture := ComputesTidily.prefix (Operation := Fin r) (framing.computes input)
        (first.computes input)
      have hcaptureTyped : captureMachine.ComputesTidily (encIn input)
          (framing.time input + first.time input)
          ((encPair encIn encMiddle) <$>
            ((fun middle => (input, middle)) <$> firstProgram input)) := by
        simpa only [Functor.map_map, Function.comp_apply, encPair_apply] using hcapture
      have hcomp := hcaptureTyped.comp_encoded (encPair encIn encMiddle)
          (prog₂ := secondProgram) true
          fun captured OracleState oracle state state' hcaptured => by
        rw [ProbOracleComp.runWith_map] at hcaptured
        obtain ⟨⟨middle, middleState⟩, hmiddle, heq⟩ :=
          (PMF.mem_support_map_iff _ _ _).mp hcaptured
        rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        have hcontinuation := second.computes (input, middle)
        have hmono : second.time (input, middle) ≤ secondOnline.totalTime input :=
          Finset.sum_le_sum fun phase _ =>
            (hsecond input OracleState oracle state middle middleState hmiddle phase).1
        exact hcontinuation.mono hmono
      simpa only [capturedProgram, bind_map_left, Function.comp_apply] using hcomp
    runsInSpace := fun input => by
      rw [totalTime_capturedAccounting]
      intro path hhead htime
      have hspace := clockedRunsInSpace_mul_time_add_one machine (encIn input)
        (5 * (framing.time input + first.time input) +
          secondOnline.totalTime input + 9) path hhead htime
      refine hspace.trans ?_
      simpa only [online, capturedAccounting, totalTime_capturedAccounting] using
        clockWorkspace_le_finishAccounting .marshalling tapes
          ((first.online.seq secondOnline).addTime .marshalling
            fun input => 5 * framing.time input + 4 * first.time input + 9) input
  }

/-- Captured sequencing retains the framing append and outer tidy-composition terms. -/
theorem machine_sequenceCaptured {Alpha Middle Beta : Type}
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
      ∀ phase,
        second.online.time phase (input, middle) ≤ secondOnline.time phase input ∧
        second.online.workspace phase (input, middle) ≤ secondOnline.workspace phase input) :
    (sequenceCaptured first second secondOnline hsecond).machine =
      second.machine.tidyComp
        (appendPTM (ofDeterministic
          (Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn).machine)
          first.machine) true :=
  rfl

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
      ∀ phase,
        second.online.time phase (input, middle) ≤ secondOnline.time phase input ∧
        second.online.workspace phase (input, middle) ≤ secondOnline.workspace phase input)
    (input : Alpha) :
    (sequenceCaptured first second secondOnline hsecond).time input =
      5 * ((Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn).time input +
        first.time input) + secondOnline.totalTime input + 9 :=
  totalTime_capturedAccounting first second secondOnline input

/-- The continuation's phase-local workspace remains visible after captured-input sequencing. -/
theorem secondWorkspace_le_sequenceCaptured {Alpha Middle Beta : Type}
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
      ∀ phase,
        second.online.time phase (input, middle) ≤ secondOnline.time phase input ∧
        second.online.workspace phase (input, middle) ≤ secondOnline.workspace phase input)
    (input : Alpha) (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (middle : Middle) (state' : OracleState)
    (hmiddle : (middle, state') ∈
      (ProbOracleComp.runWith oracle (firstProgram input) state).support)
    (phase : OnlinePhase) :
    second.online.workspace phase (input, middle) ≤
      (sequenceCaptured first second secondOnline hsecond).workspace input := by
  change second.online.workspace phase (input, middle) ≤
    (capturedAccounting first second secondOnline).totalWorkspace input
  refine (hsecond input OracleState oracle state middle state' hmiddle phase).2.trans ?_
  refine (show secondOnline.workspace phase input ≤
      ((first.online.seq secondOnline).addTime .marshalling
        (fun input =>
          5 * (Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn).time input +
            4 * first.time input + 9)).workspace phase input from
    le_max_right _ _).trans ?_
  exact workspace_le_finishAccounting .marshalling
    (max (max (Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn).tapeCount
      first.tapeCount) second.tapeCount + 2)
    ((first.online.seq secondOnline).addTime .marshalling fun input =>
      5 * (Turing.MultiTapeTM.Internal.NativeCompiler.encodeFrame encIn).time input +
        4 * first.time input + 9) phase input

/-! #### Retained bounded iteration -/

/-- Exact accounting for an input-indexed number of retained native rounds. The fixed loop machine
does not depend on `rounds input`; the schedule only certifies its per-input stopping point. The
body phase time is multiplied by one final stopping round, each body phase workspace remains its
per-round peak, and only the tape-loop scaffolding and generic clock floor are charged to the
controller. -/
@[expose] def boundedIterationAccountingOn
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha) (tapes : ℕ) :
    OnlineAccounting Alpha :=
  let roundsOnline := roundOnline.scaleBy fun input => rounds input + 1
  finishAccounting .controller tapes
    (roundsOnline.addTime .controller fun input =>
      (rounds input + 1) * (10 * lengthBound input + 23) + 8 * lengthBound input + 17)

theorem totalTime_boundedIterationAccountingOn
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha) (tapes : ℕ)
    (input : Alpha) :
    (boundedIterationAccountingOn rounds lengthBound roundOnline tapes).totalTime input =
      (rounds input + 1) *
          (roundOnline.totalTime input + 10 * lengthBound input + 23) +
        8 * lengthBound input + 17 := by
  simp only [boundedIterationAccountingOn, totalTime_finishAccounting,
    OnlineAccounting.totalTime_addTime, OnlineAccounting.totalTime_scaleBy]
  omega

/-- Every per-round phase workspace remains visible in the loop accounting. Repetition changes
time, while workspace is a peak; only controller workspace is additionally raised. -/
theorem workspace_le_boundedIterationAccountingOn
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha) (tapes : ℕ)
    (phase : OnlinePhase) (input : Alpha) :
    roundOnline.workspace phase input ≤
      (boundedIterationAccountingOn rounds lengthBound roundOnline tapes).totalWorkspace input := by
  refine (show roundOnline.workspace phase input ≤
      (boundedIterationAccountingOn rounds lengthBound roundOnline tapes).workspace phase input
    by
      by_cases hphase : phase = .controller
      · simp only [boundedIterationAccountingOn, finishAccounting,
          OnlineAccounting.withWorkspaceFloor, OnlineAccounting.addTime,
          OnlineAccounting.scaleBy, hphase, ↓reduceIte]
        exact le_max_left _ _
      · simp only [boundedIterationAccountingOn, finishAccounting,
          OnlineAccounting.withWorkspaceFloor, OnlineAccounting.addTime,
          OnlineAccounting.scaleBy, hphase, ↓reduceIte]).trans
    (OnlineAccounting.workspace_le_totalWorkspace _ phase input)

/-- Run one fixed named loop machine over typed encoded states under runtime input-indexed round,
encoded-length and phase bounds. `decoder` is used only as a proof retraction that relates the raw
kernel theorem to reachable encoded states; it is not executed by the retained machine and adds no
semantic callback. The body machine must implement and charge all parsing and output encoding.

Changing the encoded fuel changes the certified clock and semantics, not the installed machine or
its description. Normal rounds produce a nonempty encoded next state. The additional stopping
round maps the typed body result to the empty word, which `iterateWhile` treats as its
terminator. -/
@[expose] noncomputable def boundedIterationEncodedOn
    {Alpha : Type} {enc : Alpha ↪ List Bool} (decoder : Turing.MultiTapeTM.Decoder enc)
    {step : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Alpha}
    (body : NativeOracleProgram r step enc enc)
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha)
    (invariant : Alpha → ℕ → Alpha → Prop)
    (hbase : ∀ initial, invariant initial 0 initial)
    (hclock : ∀ initial n, n ≤ rounds initial → ∀ current, invariant initial n current →
      ∀ phase, body.online.time phase current ≤ roundOnline.time phase initial)
    (hworkspace : ∀ initial n, n ≤ rounds initial → ∀ current,
      invariant initial n current →
      ∀ phase, body.online.workspace phase current ≤ roundOnline.workspace phase initial)
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
      (fun input => OracleComp.iterate (rounds input) step input) enc enc := by
  letI := body.stateFintype
  let State := Turing.MultiTapePTM.IterateWhile.MachineState body.State
  letI : Fintype State := inferInstance
  let tapes := body.tapeCount + 1 + 2
  let online := boundedIterationAccountingOn rounds lengthBound roundOnline tapes
  let machine := body.machine.iterateWhile true
  let rawStep : List Bool →
      ProbOracleComp (fun _ : Fin r × List Bool => List Bool) (List Bool) :=
    fun word => enc <$> step (decoder.decode word)
  let rawInvariant (initial : Alpha) (n : ℕ) (word : List Bool) : Prop :=
    ∃ current, invariant initial n current ∧ word = enc current
  exact {
    tapeCount := tapes
    State := State
    machine := machine
    stateEncoding := iterateStateEncoding body.stateEncoding
    online := online
    computes := fun input => by
      rw [totalTime_boundedIterationAccountingOn]
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
    runsInSpace := fun input => by
      rw [totalTime_boundedIterationAccountingOn]
      intro path hhead htime
      have hspace := clockedRunsInSpace_mul_time_add_one machine (enc input)
        ((rounds input + 1) *
            (roundOnline.totalTime input + 10 * lengthBound input + 23) +
          8 * lengthBound input + 17) path hhead htime
      refine hspace.trans ?_
      simpa only [online, boundedIterationAccountingOn,
        totalTime_boundedIterationAccountingOn] using
        clockWorkspace_le_finishAccounting .controller tapes
          ((roundOnline.scaleBy (fun input => rounds input + 1)).addTime .controller fun input =>
              (rounds input + 1) * (10 * lengthBound input + 23) +
                8 * lengthBound input + 17) input
  }

/-- Typed runtime-bounded iteration retains the body loop machine exactly; the proof decoder is
absent from the installed machine and its one-entry description inventory. -/
theorem machine_boundedIterationEncodedOn
    {Alpha : Type} {enc : Alpha ↪ List Bool} (decoder : Turing.MultiTapeTM.Decoder enc)
    {step : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Alpha}
    (body : NativeOracleProgram r step enc enc)
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha)
    (invariant : Alpha → ℕ → Alpha → Prop)
    (hbase hclock hworkspace hpreserve hlast hlength) :
    (boundedIterationEncodedOn decoder body rounds lengthBound roundOnline invariant hbase hclock
      hworkspace hpreserve hlast hlength).machine = body.machine.iterateWhile true :=
  rfl

/-- Exact clock of typed runtime-indexed iteration, including its final stopping round. -/
theorem time_boundedIterationEncodedOn
    {Alpha : Type} {enc : Alpha ↪ List Bool} (decoder : Turing.MultiTapeTM.Decoder enc)
    {step : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Alpha}
    (body : NativeOracleProgram r step enc enc)
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha)
    (invariant : Alpha → ℕ → Alpha → Prop)
    (hbase hclock hworkspace hpreserve hlast hlength) (input : Alpha) :
    (boundedIterationEncodedOn decoder body rounds lengthBound roundOnline invariant hbase hclock
      hworkspace hpreserve hlast hlength).time input =
        (rounds input + 1) *
            (roundOnline.totalTime input + 10 * lengthBound input + 23) +
          8 * lengthBound input + 17 :=
  totalTime_boundedIterationAccountingOn rounds lengthBound roundOnline
    (body.tapeCount + 1 + 2) input

/-- Every invariant-reachable body phase workspace is retained as a visible peak in the typed
loop witness; it is not replaced by zero or relabeled as controller workspace. -/
theorem bodyWorkspace_le_boundedIterationEncodedOn
    {Alpha : Type} {enc : Alpha ↪ List Bool} (decoder : Turing.MultiTapeTM.Decoder enc)
    {step : Alpha → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) Alpha}
    (body : NativeOracleProgram r step enc enc)
    (rounds lengthBound : Alpha → ℕ)
    (roundOnline : OnlineAccounting Alpha)
    (invariant : Alpha → ℕ → Alpha → Prop)
    (hbase hclock hworkspace hpreserve hlast hlength)
    (initial : Alpha) (n : ℕ) (hn : n ≤ rounds initial) (current : Alpha)
    (hcurrent : invariant initial n current) (phase : OnlinePhase) :
    body.online.workspace phase current ≤
      (boundedIterationEncodedOn decoder body rounds lengthBound roundOnline invariant hbase hclock
        hworkspace hpreserve hlast hlength).workspace initial := by
  change body.online.workspace phase current ≤
    (boundedIterationAccountingOn rounds lengthBound roundOnline
      (body.tapeCount + 1 + 2)).totalWorkspace initial
  exact (hworkspace initial n hn current hcurrent phase).trans
    (workspace_le_boundedIterationAccountingOn rounds lengthBound roundOnline
      (body.tapeCount + 1 + 2) phase initial)

/-- Raw-word specialization of `boundedIterationEncodedOn`. -/
@[expose] noncomputable def boundedIterationOn
    {step : List Bool → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) (List Bool)}
    (body : NativeOracleProgram r step encBits encBits)
    (rounds lengthBound : List Bool → ℕ)
    (roundOnline : OnlineAccounting (List Bool))
    (invariant : List Bool → ℕ → List Bool → Prop)
    (hbase : ∀ initial, invariant initial 0 initial)
    (hclock : ∀ initial n, n ≤ rounds initial → ∀ word, invariant initial n word →
      ∀ phase, body.online.time phase word ≤ roundOnline.time phase initial)
    (hworkspace : ∀ initial n, n ≤ rounds initial → ∀ word,
      invariant initial n word →
      ∀ phase, body.online.workspace phase word ≤ roundOnline.workspace phase initial)
    (hpreserve : ∀ initial n, n < rounds initial → ∀ word, invariant initial n word →
      ∀ (OracleState : Type)
        (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
        (state state' : OracleState) (word' : List Bool),
        (word', state') ∈ (ProbOracleComp.runWith oracle (step word) state).support →
        invariant initial (n + 1) word' ∧ word' ≠ [])
    (hlast : ∀ initial word, invariant initial (rounds initial) word →
      ∀ (OracleState : Type)
        (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
        (state : OracleState),
        ProbOracleComp.runWith oracle (step word) state =
          ProbOracleComp.runWith oracle (pure []) state)
    (hlength : ∀ initial n, n ≤ rounds initial → ∀ word,
      invariant initial n word → word.length ≤ lengthBound initial) :
    NativeOracleProgram r
      (fun input => OracleComp.iterate (rounds input) step input) encBits encBits := by
  apply boundedIterationEncodedOn Turing.MultiTapeTM.Decoder.bits body rounds lengthBound
    roundOnline invariant hbase hclock hworkspace
  · intro initial n hn word hinvariant OracleState oracle state state' word' hword'
    have hnext :=
      hpreserve initial n hn word hinvariant OracleState oracle state state' word' hword'
    exact ⟨hnext.1, by simpa only [encBits_apply] using hnext.2⟩
  · intro initial word hinvariant OracleState oracle state
    simpa only [encBits_apply, id_map] using
      hlast initial word hinvariant OracleState oracle state
  · intro initial n hn word hinvariant
    simpa only [encBits_apply] using hlength initial n hn word hinvariant

/-- Runtime-bounded raw iteration retains one machine independently of its input fuel. -/
theorem machine_boundedIterationOn
    {step : List Bool → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) (List Bool)}
    (body : NativeOracleProgram r step encBits encBits)
    (rounds lengthBound : List Bool → ℕ)
    (roundOnline : OnlineAccounting (List Bool))
    (invariant : List Bool → ℕ → List Bool → Prop)
    (hbase hclock hworkspace hpreserve hlast hlength) :
    (boundedIterationOn body rounds lengthBound roundOnline invariant hbase hclock hworkspace
      hpreserve hlast hlength).machine = body.machine.iterateWhile true :=
  rfl

/-- Exact clock of raw-word runtime-indexed iteration. -/
theorem time_boundedIterationOn
    {step : List Bool → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) (List Bool)}
    (body : NativeOracleProgram r step encBits encBits)
    (rounds lengthBound : List Bool → ℕ)
    (roundOnline : OnlineAccounting (List Bool))
    (invariant : List Bool → ℕ → List Bool → Prop)
    (hbase hclock hworkspace hpreserve hlast hlength) (input : List Bool) :
    (boundedIterationOn body rounds lengthBound roundOnline invariant hbase hclock hworkspace
      hpreserve hlast hlength).time input =
        (rounds input + 1) *
            (roundOnline.totalTime input + 10 * lengthBound input + 23) +
          8 * lengthBound input + 17 :=
  totalTime_boundedIterationAccountingOn rounds lengthBound roundOnline
    (body.tapeCount + 1 + 2) input

/-- Fixed-round specialization of `boundedIterationOn`. -/
@[expose] noncomputable def boundedIteration
    {step : List Bool → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) (List Bool)}
    (body : NativeOracleProgram r step encBits encBits)
    (rounds lengthBound : ℕ) (roundClock roundWorkspace : OnlinePhase → ℕ)
    (invariant : List Bool → ℕ → List Bool → Prop)
    (hbase : ∀ initial, invariant initial 0 initial)
    (hclock : ∀ initial n, n ≤ rounds → ∀ word, invariant initial n word →
      ∀ phase, body.online.time phase word ≤ roundClock phase)
    (hworkspace : ∀ initial n, n ≤ rounds → ∀ word, invariant initial n word →
      ∀ phase, body.online.workspace phase word ≤ roundWorkspace phase)
    (hpreserve : ∀ initial n, n < rounds → ∀ word, invariant initial n word →
      ∀ (OracleState : Type)
        (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
        (state state' : OracleState) (word' : List Bool),
        (word', state') ∈ (ProbOracleComp.runWith oracle (step word) state).support →
        invariant initial (n + 1) word' ∧ word' ≠ [])
    (hlast : ∀ initial word, invariant initial rounds word →
      ∀ (OracleState : Type)
        (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
        (state : OracleState),
        ProbOracleComp.runWith oracle (step word) state =
          ProbOracleComp.runWith oracle (pure []) state)
    (hlength : ∀ initial n, n ≤ rounds → ∀ word,
      invariant initial n word → word.length ≤ lengthBound) :
    NativeOracleProgram r
      (fun input => OracleComp.iterate rounds step input) encBits encBits :=
  boundedIterationOn body (fun _ => rounds) (fun _ => lengthBound)
    { time := fun phase _ => roundClock phase
      workspace := fun phase _ => roundWorkspace phase }
    invariant hbase hclock hworkspace hpreserve hlast hlength

theorem machine_boundedIteration
    {step : List Bool → ProbOracleComp (fun _ : Fin r × List Bool => List Bool) (List Bool)}
    (body : NativeOracleProgram r step encBits encBits)
    (rounds lengthBound : ℕ) (roundClock roundWorkspace : OnlinePhase → ℕ)
    (invariant : List Bool → ℕ → List Bool → Prop)
    (hbase hclock hworkspace hpreserve hlast hlength) :
    (boundedIteration body rounds lengthBound roundClock roundWorkspace invariant hbase hclock
      hworkspace hpreserve hlast hlength).machine = body.machine.iterateWhile true :=
  rfl

/-- Every supported emitted result fits in the charged online clock. This follows from the actual
machine certificate; `outputBits` is not an uncharged semantic-size annotation. -/
theorem outputBits_le_time (witness : NativeOracleProgram r program encIn encOut)
    {OracleState : Type}
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (input : Alpha) (state : OracleState) {output : Beta} {finalState : OracleState}
    (houtput : (output, finalState) ∈
      (ProbOracleComp.runWith oracle (program input) state).support) :
    witness.outputBits output ≤ witness.time input := by
  have hencoded : (encOut output, finalState) ∈
      (ProbOracleComp.runWith oracle (encOut <$> program input) state).support := by
    rw [ProbOracleComp.runWith_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨(output, finalState), houtput, rfl⟩
  exact (witness.computes input).length_output_le oracle state hencoded

/-- The exact first-order description of the recorded native machine. -/
@[expose] noncomputable def description (witness : NativeOracleProgram r program encIn encOut) :
    Turing.MultiTapePTM.Universal.Desc := by
  letI := witness.stateFintype
  exact Description.ofMachine witness.stateEncoding witness.machine

/-- The recorded description is the explicit finite enumeration of the packaged open machine. -/
theorem description_eq_ofMachine (witness : NativeOracleProgram r program encIn encOut) :
    witness.description =
      @Description.ofMachine witness.tapeCount r witness.State witness.stateFintype
        witness.stateEncoding witness.machine :=
  rfl

/-- Encoding an artifact's typed output preserves its exact first-order description. -/
theorem description_encodedOutput (witness : NativeOracleProgram r program encIn encOut) :
    witness.encodedOutput.description = witness.description :=
  rfl

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

/-- The generated description realizes the same complete output/external-state law as the named
Boolean machine, modulo the explicit symbol encoding. This is the run-level link missing from
mere transition-table correspondence. -/
theorem runWith_descriptionRun (witness : NativeOracleProgram r program encIn encOut)
    {OracleState : Type}
    (handler : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (input : Alpha) (state : OracleState) :
    ProbOracleComp.runWith handler (witness.descriptionRun input) state =
      (ProbOracleComp.runWith handler (encOut <$> program input) state).map
        (Prod.map (List.map Turing.MultiTapeTM.Universal.eBit) id) := by
  letI := witness.stateFintype
  rw [descriptionRun, show witness.description.toMachine.initialConfig
      ((encIn input).map Turing.MultiTapeTM.Universal.eBit) =
        Description.mapConfig witness.stateEncoding
          (witness.machine.initialConfig (encIn input)) by
      exact (Description.mapConfig_initial witness.stateEncoding witness.machine
        (encIn input)).symm]
  simp only [MultiTapePTM.runFrom, ProbOracleComp.runWith_map]
  rw [Description.runWith_ofMachine]
  rw [PMF.map_map]
  have hnative := (witness.computes input).runOracle handler state
  rw [MultiTapePTM.runOracle_eq_map, ProbOracleComp.runWith_map] at hnative
  rw [← hnative, PMF.map_map]
  congr 1
  funext result
  rcases result with ⟨cfg, finalState⟩
  rfl

/-- Exact unary-model static length of the named open machine. -/
@[expose] noncomputable def staticBits (witness : NativeOracleProgram r program encIn encOut) : ℕ :=
  Turing.MultiTapePTM.Universal.descLen witness.description

/-- Static bits are definitionally the length of the recorded first-order description. -/
theorem staticBits_eq_descLen (witness : NativeOracleProgram r program encIn encOut) :
    witness.staticBits = Turing.MultiTapePTM.Universal.descLen witness.description :=
  rfl

/-- Encoding an artifact's typed output adds no installed static bits. -/
theorem staticBits_encodedOutput (witness : NativeOracleProgram r program encIn encOut) :
    witness.encodedOutput.staticBits = witness.staticBits :=
  rfl

/-- The concrete installed-description inventory for one packaged native artifact. A composed
witness installs its final composed description once: the inlined constructor and component
controls are not additional installed copies. External services and separately retained compilers
must appear in their own inventories. -/
@[expose] noncomputable def installedDescriptions
    (witness : NativeOracleProgram r program encIn encOut) :
    List Turing.MultiTapePTM.Universal.Desc :=
  [witness.description]

/-- Every packaged witness exposes its exact one-occurrence installed inventory. -/
theorem installedDescriptions_eq_singleton
    (witness : NativeOracleProgram r program encIn encOut) :
    witness.installedDescriptions = [witness.description] :=
  rfl

/-- Encoding an artifact's typed output neither adds nor duplicates an installed occurrence. -/
theorem installedDescriptions_encodedOutput
    (witness : NativeOracleProgram r program encIn encOut) :
    witness.encodedOutput.installedDescriptions = witness.installedDescriptions :=
  rfl

/-- Exact unary-model size of the explicit installed-description inventory. -/
@[expose] noncomputable def installedBits
    (witness : NativeOracleProgram r program encIn encOut) : ℕ :=
  (witness.installedDescriptions.map Turing.MultiTapePTM.Universal.descLen).sum

/-- A packaged native artifact's one-entry installed inventory is exactly its static charge. -/
theorem installedBits_eq_staticBits (witness : NativeOracleProgram r program encIn encOut) :
    witness.installedBits = witness.staticBits := by
  simp [installedBits, installedDescriptions, staticBits]

/-- Conditional arithmetic charge for a caller-supplied copy count. This helper does not determine
which artifacts are installed, whether copies are shared, or whether a composed artifact already
inlines its components; that inventory belongs to the consuming construction. -/
@[expose] noncomputable def staticBitsCopies (count : ℕ)
    (witness : NativeOracleProgram r program encIn encOut) : ℕ :=
  count * witness.staticBits

theorem staticBitsCopies_one (witness : NativeOracleProgram r program encIn encOut) :
    staticBitsCopies 1 witness = witness.staticBits := by
  simp [staticBitsCopies]

end NativeOracleProgram

end Turing.MultiTapePTM.Internal

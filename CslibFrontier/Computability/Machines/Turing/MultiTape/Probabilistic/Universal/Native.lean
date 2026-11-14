/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.FirstMatch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Replicate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Universal
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.FirstOrder

/-!
# Retained native first-order oracle-machine primitives

This module instantiates the lower named compiler constructions for the first-order probabilistic
description layer. It initializes `ICfg` by executing retained projection, comparison, unary-list
conversion, replication and pairing machines. It also exposes transition-table first-match lookup
through the generic retained stream compiler, executes local actions, validates query commands and
installs replies with retained indexed list updates.

The external oracle execution, dynamic physical-channel dispatch and runtime iteration controller
remain outside this module. Lookup, tag/coin dispatch and local execution are exposed as separate
compiler stages; the aggregate `commandAtCompiler` performs the table scan exactly once.

## Main definitions

* `Turing.MultiTapePTM.Universal.Desc.tapesCompiler`, `.statesCompiler`,
  `.operationsCompiler`, `.initialCompiler`, `.tableCompiler`: retained description projections.
* `Turing.MultiTapePTM.Universal.ICfg.initCompiler`: retained exact initialization.
* `Turing.MultiTapePTM.Universal.ICfg.localStepCompiler`, `.commandCompiler`: retained local and
  validated-query command construction.
* `Turing.MultiTapePTM.Universal.ICfg.commandAtLookupStageCompiler`,
  `.commandAtFromLookupCompiler`, `.commandAtCompiler`: separately chargeable lookup/post-lookup
  stages and their single-scan aggregate.
* `Turing.MultiTapePTM.Universal.ICfg.receiveCompiler`: retained indexed reply installation.
* `Turing.MultiTapePTM.Universal.firstMatchCompiler`: retained first-match table lookup.
-/

@[expose] public section

namespace Turing.MultiTapePTM.Universal

open Turing.MultiTapeTM
open Turing.MultiTapeTM.Internal

private abbrev DescTail₄ := ℕ × ℕ × ℕ × List (Key × Branches)
private abbrev DescTail₃ := ℕ × ℕ × List (Key × Branches)
private abbrev DescTail₂ := ℕ × List (Key × Branches)

private abbrev eDescTail₄ : DescTail₄ ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary (encList (encPair eKey eBranches))))
private abbrev eDescTail₃ : DescTail₃ ↪ List Bool :=
  encPair encUnary (encPair encUnary (encList (encPair eKey eBranches)))
private abbrev eDescTail₂ : DescTail₂ ↪ List Bool :=
  encPair encUnary (encList (encPair eKey eBranches))

private abbrev ICfgTail₄ := ℕ × List Turing.MultiTapeTM.Universal.Tape × List ℕ × List Channel
private abbrev ICfgTail₃ := List Turing.MultiTapeTM.Universal.Tape × List ℕ × List Channel
private abbrev ICfgTail₂ := List ℕ × List Channel

private abbrev eICfgTail₄ : ICfgTail₄ ↪ List Bool :=
  encPair encNat (encPair (encList Turing.MultiTapeTM.Universal.eTape)
    (encPair (encList encUnary) (encList eChannel)))
private abbrev eICfgTail₃ : ICfgTail₃ ↪ List Bool :=
  encPair (encList Turing.MultiTapeTM.Universal.eTape)
    (encPair (encList encUnary) (encList eChannel))
private abbrev eICfgTail₂ : ICfgTail₂ ↪ List Bool :=
  encPair (encList encUnary) (encList eChannel)

private abbrev StepPayload := Turing.MultiTapeTM.Universal.Act ×
  (List (Option ℕ) × List SignType)
private abbrev QueryPayload := ℕ × ℕ
private abbrev eStepPayload : StepPayload ↪ List Bool :=
  encPair Turing.MultiTapeTM.Universal.eAct
    (encPair (encList Turing.MultiTapeTM.Universal.eSym) (encList encSign))
private abbrev eQueryPayload : QueryPayload ↪ List Bool := encPair encUnary encUnary
private abbrev ChannelTail := List ℕ × ℤ
private abbrev eChannelTail : ChannelTail ↪ List Bool :=
  encPair (encList encUnary) Turing.MultiTapeTM.Universal.encIntUnary
private abbrev KeyInput := List ℕ × (ICfg × ℕ)
private abbrev eKeyInput : KeyInput ↪ List Bool :=
  encPair (encList encUnary) (encPair eICfg encUnary)
private abbrev ReceiveInput (r : ℕ) := ICfg × (Fin r × (ℕ × List ℕ))
private abbrev eReceiveInput (r : ℕ) : ReceiveInput r ↪ List Bool :=
  encPair eICfg (encPair (eOperation r) (encPair encUnary (encList encUnary)))
private abbrev ChannelStepInput := Channel × (Option ℕ × SignType)
private abbrev eChannelStepInput : ChannelStepInput ↪ List Bool :=
  encPair eChannel (encPair eSym encSign)
private abbrev ChannelsStepInput := List Channel × (List (Option ℕ) × List SignType)
private abbrev eChannelsStepInput : ChannelsStepInput ↪ List Bool :=
  encPair (encList eChannel) (encPair (encList eSym) (encList encSign))
private abbrev CommandAtInput := Desc × (List ℕ × (ICfg × Bool))
private abbrev eCommandAtInput : CommandAtInput ↪ List Bool :=
  encPair eDesc (encPair (encList encUnary) (encPair eICfg encBool))
private abbrev CommandAtLookupInput := CommandAtInput × Option Branches
private abbrev eCommandAtLookupInput : CommandAtLookupInput ↪ List Bool :=
  encPair eCommandAtInput (encOption eBranches)

/-- Retained projection of the declared work-tape count. -/
noncomputable def Desc.tapesCompiler : NativeCompiler Desc.tapes eDesc encUnary :=
  (NativeCompiler.first encUnary eDescTail₄).ofInputEq
    (fun d => (d.tapes, d.states, d.operations, d.q₀, d.table)) fun _ => rfl

/-- Retained projection of the description tail after the tape count. -/
noncomputable def Desc.tail₄Compiler :
    NativeCompiler (fun d : Desc => (d.states, d.operations, d.q₀, d.table)) eDesc eDescTail₄ :=
  (NativeCompiler.second encUnary eDescTail₄).ofInputEq
    (fun d => (d.tapes, d.states, d.operations, d.q₀, d.table)) fun _ => rfl

/-- Retained projection of the declared user-state count. -/
noncomputable def Desc.statesCompiler : NativeCompiler Desc.states eDesc encUnary :=
  ((NativeCompiler.first encUnary eDescTail₃).comp Desc.tail₄Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of the description tail after the state count. -/
noncomputable def Desc.tail₃Compiler :
    NativeCompiler (fun d : Desc => (d.operations, d.q₀, d.table)) eDesc eDescTail₃ :=
  ((NativeCompiler.second encUnary eDescTail₃).comp Desc.tail₄Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of the declared oracle-operation count. -/
noncomputable def Desc.operationsCompiler : NativeCompiler Desc.operations eDesc encUnary :=
  ((NativeCompiler.first encUnary eDescTail₂).comp Desc.tail₃Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of the description tail after the operation count. -/
noncomputable def Desc.tail₂Compiler :
    NativeCompiler (fun d : Desc => (d.q₀, d.table)) eDesc eDescTail₂ :=
  ((NativeCompiler.second encUnary eDescTail₂).comp Desc.tail₃Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of the initial-state tag. -/
noncomputable def Desc.initialCompiler : NativeCompiler Desc.q₀ eDesc encUnary :=
  ((NativeCompiler.first encUnary (encList (encPair eKey eBranches))).comp
    Desc.tail₂Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of the complete transition table. -/
noncomputable def Desc.tableCompiler :
    NativeCompiler Desc.table eDesc (encList (encPair eKey eBranches)) :=
  ((NativeCompiler.second encUnary (encList (encPair eKey eBranches))).comp
    Desc.tail₂Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of the nested optional control. -/
noncomputable def ICfg.controlCompiler :
    NativeCompiler ICfg.control eICfg (encOption (encOption encUnary)) :=
  (NativeCompiler.first (encOption (encOption encUnary)) eICfgTail₄).ofInputEq
    (fun cfg => (cfg.control, cfg.inputPos, cfg.workTapes, cfg.output, cfg.channels)) fun _ => rfl

/-- Retained projection of the first-order configuration tail after control. -/
noncomputable def ICfg.tail₄Compiler :
    NativeCompiler (fun cfg : ICfg => (cfg.inputPos, cfg.workTapes, cfg.output, cfg.channels))
      eICfg eICfgTail₄ :=
  (NativeCompiler.second (encOption (encOption encUnary)) eICfgTail₄).ofInputEq
    (fun cfg => (cfg.control, cfg.inputPos, cfg.workTapes, cfg.output, cfg.channels)) fun _ => rfl

/-- Retained projection of the input-head position. -/
noncomputable def ICfg.inputPosCompiler : NativeCompiler ICfg.inputPos eICfg encNat :=
  ((NativeCompiler.first encNat eICfgTail₃).comp ICfg.tail₄Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of the first-order configuration tail after input position. -/
noncomputable def ICfg.tail₃Compiler :
    NativeCompiler (fun cfg : ICfg => (cfg.workTapes, cfg.output, cfg.channels))
      eICfg eICfgTail₃ :=
  ((NativeCompiler.second encNat eICfgTail₃).comp ICfg.tail₄Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of the work-tape list. -/
noncomputable def ICfg.workTapesCompiler :
    NativeCompiler ICfg.workTapes eICfg (encList Turing.MultiTapeTM.Universal.eTape) :=
  ((NativeCompiler.first (encList Turing.MultiTapeTM.Universal.eTape) eICfgTail₂).comp
    ICfg.tail₃Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of the first-order configuration tail after work tapes. -/
noncomputable def ICfg.tail₂Compiler :
    NativeCompiler (fun cfg : ICfg => (cfg.output, cfg.channels)) eICfg eICfgTail₂ :=
  ((NativeCompiler.second (encList Turing.MultiTapeTM.Universal.eTape) eICfgTail₂).comp
    ICfg.tail₃Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of accumulated output. -/
noncomputable def ICfg.outputCompiler :
    NativeCompiler ICfg.output eICfg (encList encUnary) :=
  ((NativeCompiler.first (encList encUnary) (encList eChannel)).comp
    ICfg.tail₂Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of channel storage. -/
noncomputable def ICfg.channelsCompiler :
    NativeCompiler ICfg.channels eICfg (encList eChannel) :=
  ((NativeCompiler.second (encList encUnary) (encList eChannel)).comp
    ICfg.tail₂Compiler).ofOutputEq fun _ => rfl

/-- Retained projection of a channel's pending query. -/
noncomputable def Channel.queryCompiler :
    NativeCompiler Channel.query eChannel (encList encUnary) :=
  (NativeCompiler.first (encList encUnary)
    (encPair (encList encUnary) Turing.MultiTapeTM.Universal.encIntUnary)).ofInputEq
      (fun channel => (channel.query, channel.answer, channel.answerPos)) fun _ => rfl

/-- Retained projection of installed answer storage and its signed head position. -/
noncomputable def Channel.tailCompiler :
    NativeCompiler (fun channel : Channel => (channel.answer, channel.answerPos))
      eChannel eChannelTail :=
  (NativeCompiler.second (encList encUnary) eChannelTail).ofInputEq
    (fun channel => (channel.query, channel.answer, channel.answerPos)) fun _ => rfl

/-- Retained projection of installed answer storage. -/
noncomputable def Channel.answerCompiler :
    NativeCompiler Channel.answer eChannel (encList encUnary) :=
  (NativeCompiler.first (encList encUnary)
    Turing.MultiTapeTM.Universal.encIntUnary).comp Channel.tailCompiler

/-- Retained projection of the signed answer-head position. -/
noncomputable def Channel.answerPosCompiler :
    NativeCompiler Channel.answerPos eChannel Turing.MultiTapeTM.Universal.encIntUnary :=
  (NativeCompiler.second (encList encUnary)
    Turing.MultiTapeTM.Universal.encIntUnary).comp Channel.tailCompiler

/-- Retained answer-head read. Negative and out-of-range positions emit blank; nonnegative
positions execute the charged binary-indexed list scan. -/
noncomputable def Channel.readCompiler : NativeCompiler Channel.read eChannel eSym := by
  let nonnegative := NativeCompiler.intUnaryNonnegativeTest.comp Channel.answerPosCompiler
  let index := NativeCompiler.intUnaryPayloadCompiler.comp Channel.answerPosCompiler
  let lookup := (NativeCompiler.listGet?NatCompiler encUnary).comp
    (Channel.answerCompiler.pair index)
  let blank := NativeCompiler.const eChannel eSym none
  refine (NativeCompiler.ite nonnegative lookup blank).ofOutputEq ?_
  intro channel
  cases channel.answerPos <;> simp [Channel.read, NativeCompiler.intUnaryPayload]

/-- Retained reply installation for one channel: clear the query, install the reply and reset the
signed answer position to zero. -/
noncomputable def Channel.receiveCompiler :
    NativeCompiler Channel.receive (encList encUnary) eChannel := by
  let query := NativeCompiler.const (encList encUnary) (encList encUnary) []
  let answer := NativeCompiler.identity (encList encUnary)
  let position := NativeCompiler.const (encList encUnary)
    Turing.MultiTapeTM.Universal.encIntUnary 0
  exact query.pair (answer.pair position) |>.ofOutputEq fun _ => rfl

/-- Retained one-channel local step, including query append and signed answer-head movement. -/
noncomputable def Channel.stepCompiler :
    NativeCompiler (fun input : ChannelStepInput => input.1.step input.2.1 input.2.2)
      eChannelStepInput eChannel := by
  let channel := NativeCompiler.first eChannel (encPair eSym encSign)
  let action := NativeCompiler.second eChannel (encPair eSym encSign)
  let symbol := (NativeCompiler.first eSym encSign).comp action
  let movement := (NativeCompiler.second eSym encSign).comp action
  let query := Channel.queryCompiler.comp channel
  let answer := Channel.answerCompiler.comp channel
  let position := Channel.answerPosCompiler.comp channel
  let appended := (NativeCompiler.listAppendCompiler encUnary).comp
    (query.pair ((NativeCompiler.optionToListCompiler encUnary).comp symbol))
  let moved := NativeCompiler.intMove.comp (position.pair movement)
  exact appended.pair (answer.pair moved) |>.ofOutputEq fun _ => rfl

private theorem channelsZip_eq_mapIdx (channels : List Channel)
    (querySymbols : List (Option ℕ)) (answerMoves : List SignType) :
    NativeCompiler.listZipWithLeft .zero
        (fun input : (Channel × Option ℕ) × SignType => input.1.1.step input.1.2 input.2)
        (NativeCompiler.listZipWithLeft none Prod.mk channels querySymbols) answerMoves =
      channels.mapIdx fun operation channel =>
        channel.step (querySymbols.getD operation none) (answerMoves.getD operation 0) := by
  induction channels generalizing querySymbols answerMoves with
  | nil => rfl
  | cons channel channels ih =>
      cases querySymbols <;> cases answerMoves <;>
        simp [NativeCompiler.listZipWithLeft, ih]

/-- Retained per-channel local updates. The two explicit left-length scans pair query writes and
answer moves with every stored channel, including their defaults. -/
noncomputable def ICfg.channelsStepCompiler :
    NativeCompiler
      (fun input : ChannelsStepInput => input.1.mapIdx fun operation channel =>
        channel.step (input.2.1.getD operation none) (input.2.2.getD operation 0))
      eChannelsStepInput (encList eChannel) := by
  let channels := NativeCompiler.first (encList eChannel)
    (encPair (encList eSym) (encList encSign))
  let actions := NativeCompiler.second (encList eChannel)
    (encPair (encList eSym) (encList encSign))
  let querySymbols := (NativeCompiler.first (encList eSym) (encList encSign)).comp actions
  let answerMoves := (NativeCompiler.second (encList eSym) (encList encSign)).comp actions
  let pairChannelSymbol := NativeCompiler.identity (encPair eChannel eSym)
  let withQueries := (NativeCompiler.listZipWithLeftCompiler none eChannel eSym
    (encPair eChannel eSym) pairChannelSymbol).comp (channels.pair querySymbols)
  let encChannelSymbol := encPair eChannel eSym
  let channelSymbolStep : NativeCompiler
      (fun input : (Channel × Option ℕ) × SignType => input.1.1.step input.1.2 input.2)
      (encPair encChannelSymbol encSign) eChannel := by
    let channelSymbol := NativeCompiler.first encChannelSymbol encSign
    let movement := NativeCompiler.second encChannelSymbol encSign
    let channel := (NativeCompiler.first eChannel eSym).comp channelSymbol
    let symbol := (NativeCompiler.second eChannel eSym).comp channelSymbol
    exact Channel.stepCompiler.comp (channel.pair (symbol.pair movement))
  let stepped := (NativeCompiler.listZipWithLeftCompiler .zero encChannelSymbol encSign
    eChannel channelSymbolStep).comp (withQueries.pair answerMoves)
  exact stepped.ofOutputEq fun input =>
    congrArg (encList eChannel) (channelsZip_eq_mapIdx input.1 input.2.1 input.2.2).symm

/-- Retained answer-head reads, executing the named channel-read callback once per channel. -/
noncomputable def ICfg.answerSymbolsCompiler :
    NativeCompiler ICfg.answerSymbols eICfg (encList eSym) :=
  (NativeCompiler.listMapCompiler eChannel eSym Channel.readCompiler).comp
    ICfg.channelsCompiler

/-- Retained work-head reads, executing the named zipper-read callback once per work tape. -/
noncomputable def ICfg.workSymbolsCompiler :
    NativeCompiler ICfg.workSymbols eICfg (encList eSym) :=
  NativeCompiler.reads.comp ICfg.workTapesCompiler

/-- Retained first-order transition-key construction. Input, work-tape and answer-channel reads
are all named native scans; the supplied state tag is framed with their results. -/
noncomputable def ICfg.keyCompiler :
    NativeCompiler (fun input : KeyInput => input.2.1.key input.1 input.2.2)
      eKeyInput eKey := by
  let word := NativeCompiler.first (encList encUnary) (encPair eICfg encUnary)
  let tail := NativeCompiler.second (encList encUnary) (encPair eICfg encUnary)
  let cfg := (NativeCompiler.first eICfg encUnary).comp tail
  let state := (NativeCompiler.second eICfg encUnary).comp tail
  let position := ICfg.inputPosCompiler.comp cfg
  let inputHead := NativeCompiler.inputSymbol.comp (word.pair position)
  let workHeads := ICfg.workSymbolsCompiler.comp cfg
  let answerHeads := ICfg.answerSymbolsCompiler.comp cfg
  let fields := state.pair (inputHead.pair (workHeads.pair answerHeads))
  exact fields.ofOutputEq fun _ => rfl

/-- Retained checked-channel reply installation. The selected channel is replaced by a full
charged list scan; if first-order storage is malformed and too short, the list is unchanged just
as in `List.modify`. -/
noncomputable def ICfg.receiveCompiler (r : ℕ) :
    NativeCompiler
      (fun input : ReceiveInput r =>
        input.1.receive input.2.1 input.2.2.1 input.2.2.2)
      (eReceiveInput r) eICfg := by
  let encTail := encPair (eOperation r) (encPair encUnary (encList encUnary))
  let cfg := NativeCompiler.first eICfg encTail
  let tail := NativeCompiler.second eICfg encTail
  let operation := (NativeCompiler.first (eOperation r)
    (encPair encUnary (encList encUnary))).comp tail
  let nextReply := (NativeCompiler.second (eOperation r)
    (encPair encUnary (encList encUnary))).comp tail
  let next := (NativeCompiler.first encUnary (encList encUnary)).comp nextReply
  let reply := (NativeCompiler.second encUnary (encList encUnary)).comp nextReply
  let operationNat := operation.ofOutputEq (g := fun input : ReceiveInput r => input.2.1.val)
    fun _ => rfl
  let channel := Channel.receiveCompiler.comp reply
  let channels := ICfg.channelsCompiler.comp cfg
  let updatedChannels := (NativeCompiler.listReplaceUnaryCompiler eChannel).comp
    (channels.pair (operationNat.pair channel))
  let control := (NativeCompiler.optionSome (encOption encUnary)).comp
    ((NativeCompiler.optionSome encUnary).comp next)
  let inputPos := ICfg.inputPosCompiler.comp cfg
  let workTapes := ICfg.workTapesCompiler.comp cfg
  let output := ICfg.outputCompiler.comp cfg
  let fields := control.pair
    (inputPos.pair (workTapes.pair (output.pair updatedChannels)))
  exact fields.ofOutputEq fun _ => rfl

/-- Retained first-order local halt, preserving every field except control. -/
noncomputable def ICfg.haltCompiler : NativeCompiler ICfg.halt eICfg eICfg := by
  let halted := NativeCompiler.const eICfg (encOption (encOption encUnary)) none
  let fields := halted.pair (ICfg.inputPosCompiler.pair
    (ICfg.workTapesCompiler.pair (ICfg.outputCompiler.pair ICfg.channelsCompiler)))
  exact fields.ofOutputEq fun _ => rfl

/-- Total ordinary-step payload with the explicit inhabited default on query actions. -/
def Act.stepPayload (action : Act) : StepPayload :=
  Sum.elim id (Function.const QueryPayload default) (eAct_toSum action)

/-- Total query payload with zero tags on ordinary-step actions. -/
def Act.queryPayload (action : Act) : QueryPayload :=
  Sum.elim (Function.const StepPayload (0, 0)) id (eAct_toSum action)

/-- Retained ordinary-step payload extraction from the actual action constructor tag. -/
noncomputable def Act.stepPayloadCompiler : NativeCompiler Act.stepPayload eAct eStepPayload :=
  (NativeCompiler.sumLeftD default eStepPayload eQueryPayload).ofInputEq eAct_toSum fun _ => rfl

/-- Retained query payload extraction from the actual action constructor tag. -/
noncomputable def Act.queryPayloadCompiler : NativeCompiler Act.queryPayload eAct eQueryPayload :=
  (NativeCompiler.sumRightD (0, 0) eStepPayload eQueryPayload).ofInputEq eAct_toSum fun _ => rfl

private abbrev CommandInput := Desc × (List ℕ × (ICfg × Act))
private abbrev eCommandInput : CommandInput ↪ List Bool :=
  encPair eDesc (encPair (encList encUnary) (encPair eICfg eAct))

private noncomputable def commandDescCompiler : NativeCompiler Prod.fst eCommandInput eDesc :=
  NativeCompiler.first eDesc (encPair (encList encUnary) (encPair eICfg eAct))

private noncomputable def commandTailCompiler :
    NativeCompiler Prod.snd eCommandInput (encPair (encList encUnary) (encPair eICfg eAct)) :=
  NativeCompiler.second eDesc (encPair (encList encUnary) (encPair eICfg eAct))

private noncomputable def commandInputCompiler :
    NativeCompiler (fun input : CommandInput => input.2.1) eCommandInput (encList encUnary) :=
  (NativeCompiler.first (encList encUnary) (encPair eICfg eAct)).comp commandTailCompiler

private noncomputable def commandCfgActCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2) eCommandInput (encPair eICfg eAct) :=
  (NativeCompiler.second (encList encUnary) (encPair eICfg eAct)).comp commandTailCompiler

private noncomputable def commandCfgCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2.1) eCommandInput eICfg :=
  (NativeCompiler.first eICfg eAct).comp commandCfgActCompiler

private noncomputable def commandActCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2.2) eCommandInput eAct :=
  (NativeCompiler.second eICfg eAct).comp commandCfgActCompiler

private noncomputable def commandQueryPayloadCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2.2.queryPayload)
      eCommandInput eQueryPayload :=
  Act.queryPayloadCompiler.comp commandActCompiler

private noncomputable def commandOperationCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2.2.queryPayload.1)
      eCommandInput encUnary :=
  (NativeCompiler.first encUnary encUnary).comp commandQueryPayloadCompiler

private noncomputable def commandNextCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2.2.queryPayload.2)
      eCommandInput encUnary :=
  (NativeCompiler.second encUnary encUnary).comp commandQueryPayloadCompiler

private noncomputable def commandStepPayloadCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2.2.stepPayload)
      eCommandInput eStepPayload :=
  Act.stepPayloadCompiler.comp commandActCompiler

private noncomputable def commandOrdinaryCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2.2.stepPayload.1)
      eCommandInput Turing.MultiTapeTM.Universal.eAct :=
  (NativeCompiler.first Turing.MultiTapeTM.Universal.eAct
    (encPair (encList Turing.MultiTapeTM.Universal.eSym) (encList encSign))).comp
      commandStepPayloadCompiler

private noncomputable def commandStepTailCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2.2.stepPayload.2)
      eCommandInput
      (encPair (encList Turing.MultiTapeTM.Universal.eSym) (encList encSign)) :=
  (NativeCompiler.second Turing.MultiTapeTM.Universal.eAct
    (encPair (encList Turing.MultiTapeTM.Universal.eSym) (encList encSign))).comp
      commandStepPayloadCompiler

private noncomputable def commandQuerySymbolsCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2.2.stepPayload.2.1)
      eCommandInput (encList Turing.MultiTapeTM.Universal.eSym) :=
  (NativeCompiler.first (encList Turing.MultiTapeTM.Universal.eSym)
    (encList encSign)).comp commandStepTailCompiler

private noncomputable def commandAnswerMovesCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2.2.stepPayload.2.2)
      eCommandInput (encList encSign) :=
  (NativeCompiler.second (encList Turing.MultiTapeTM.Universal.eSym)
    (encList encSign)).comp commandStepTailCompiler

private noncomputable def commandOperationsCompiler :
    NativeCompiler (fun input : CommandInput => input.1.operations) eCommandInput encUnary :=
  Desc.operationsCompiler.comp commandDescCompiler

private noncomputable def commandStatesCompiler :
    NativeCompiler (fun input : CommandInput => input.1.states) eCommandInput encUnary :=
  Desc.statesCompiler.comp commandDescCompiler

/-- Retained validation of an optional ordinary successor tag. -/
noncomputable def ICfg.nextIControlCompiler :
    NativeCompiler (fun input : ℕ × Option ℕ => nextIControl input.1 input.2)
      (encPair encUnary Turing.MultiTapeTM.Universal.eSym)
      (encOption Turing.MultiTapeTM.Universal.eSym) := by
  let states := NativeCompiler.first encUnary Turing.MultiTapeTM.Universal.eSym
  let next := NativeCompiler.second encUnary Turing.MultiTapeTM.Universal.eSym
  let hasNext := (NativeCompiler.optionIsSomeTest encUnary).comp next
  let tag := (NativeCompiler.optionGetD 0 encUnary).comp next
  let inRange := NativeCompiler.unaryLtTest.comp (tag.pair states)
  let valid := (NativeCompiler.optionSome Turing.MultiTapeTM.Universal.eSym).comp
    ((NativeCompiler.optionSome encUnary).comp tag)
  let halt := NativeCompiler.const
    (encPair encUnary Turing.MultiTapeTM.Universal.eSym)
    (encOption Turing.MultiTapeTM.Universal.eSym) none
  refine (NativeCompiler.ite hasNext (NativeCompiler.ite inRange valid halt) halt).ofOutputEq ?_
  rintro ⟨states, next⟩
  cases next with
  | none => rfl
  | some next => by_cases h : next < states <;> simp [nextIControl, h]

/-- Retained ordinary local step on the command input layout. Every field update remains a named
constituent compiler so phase-aware consumers can charge local execution separately. -/
noncomputable def ICfg.localStepCompiler :
    NativeCompiler
      (fun input : Desc × (List ℕ × (ICfg × Act)) =>
        input.2.2.1.step input.2.1 input.1.states input.2.2.2.stepPayload.1
          input.2.2.2.stepPayload.2.1 input.2.2.2.stepPayload.2.2)
      (encPair eDesc (encPair (encList encUnary) (encPair eICfg eAct))) eICfg := by
  let ordinary := commandOrdinaryCompiler
  let next := NativeCompiler.actState.comp ordinary
  let control := ICfg.nextIControlCompiler.comp (commandStatesCompiler.pair next)
  let position := ICfg.inputPosCompiler.comp commandCfgCompiler
  let inputHead := NativeCompiler.inputSymbol.comp (commandInputCompiler.pair position)
  let inputMove := NativeCompiler.actInputMove.comp ordinary
  let movedInput := NativeCompiler.moveInput.comp (position.pair (inputHead.pair inputMove))
  let workActions := NativeCompiler.actWorkActions.comp ordinary
  let movedWork := NativeCompiler.applyTapes.comp
    ((ICfg.workTapesCompiler.comp commandCfgCompiler).pair workActions)
  let outputSymbol := NativeCompiler.actOutput.comp ordinary
  let output := (NativeCompiler.listAppendCompiler encUnary).comp
    ((ICfg.outputCompiler.comp commandCfgCompiler).pair
      ((NativeCompiler.optionToListCompiler encUnary).comp outputSymbol))
  let channels := ICfg.channelsStepCompiler.comp
    ((ICfg.channelsCompiler.comp commandCfgCompiler).pair
      (commandQuerySymbolsCompiler.pair commandAnswerMovesCompiler))
  let fields := control.pair (movedInput.pair (movedWork.pair (output.pair channels)))
  exact fields.ofOutputEq fun _ => rfl

private noncomputable def commandChannelsCompiler :
    NativeCompiler (fun input : CommandInput => input.2.2.1.channels)
      eCommandInput (encList eChannel) :=
  ICfg.channelsCompiler.comp commandCfgCompiler

private noncomputable def commandRequestCompiler :
    NativeCompiler
      (fun input : CommandInput =>
        (input.2.2.1.channels.getD input.2.2.2.queryPayload.1 Channel.blank).query)
      eCommandInput (encList encUnary) :=
  Channel.queryCompiler.comp
    ((NativeCompiler.listGetDUnary Channel.blank eChannel).comp
      (commandChannelsCompiler.pair commandOperationCompiler))

private noncomputable def commandHaltWordCompiler :
    NativeCompiler (fun input : CommandInput => false :: eICfg input.2.2.1.halt)
      eCommandInput encBits :=
  (NativeCompiler.prefixBit false).comp (ICfg.haltCompiler.comp commandCfgCompiler)

private noncomputable def commandQueryWordCompiler :
    NativeCompiler
      (fun input : CommandInput => true ::
        encPair encUnary
          (encPair (encList encUnary) (encPair encUnary eICfg))
          (input.2.2.2.queryPayload.1,
            (input.2.2.1.channels.getD input.2.2.2.queryPayload.1 Channel.blank).query,
            input.2.2.2.queryPayload.2, input.2.2.1))
      eCommandInput encBits := by
  let payload := commandOperationCompiler.pair
    (commandRequestCompiler.pair (commandNextCompiler.pair commandCfgCompiler))
  exact (NativeCompiler.prefixBit true).comp payload

/-- Retained validated query path. Invalid description counts, operation tags and successor tags
emit the exact locally halted command word. -/
noncomputable def ICfg.queryCommandWordCompiler (r : ℕ) :
    NativeCompiler
      (fun input : CommandInput =>
        if input.1.operations = r then
          if input.2.2.2.queryPayload.1 < r then
            if input.2.2.2.queryPayload.2 < input.1.states then
              true :: encPair encUnary
                (encPair (encList encUnary) (encPair encUnary eICfg))
                (input.2.2.2.queryPayload.1,
                  (input.2.2.1.channels.getD input.2.2.2.queryPayload.1 Channel.blank).query,
                  input.2.2.2.queryPayload.2, input.2.2.1)
            else false :: eICfg input.2.2.1.halt
          else false :: eICfg input.2.2.1.halt
        else false :: eICfg input.2.2.1.halt)
      eCommandInput encBits := by
  let countMatches := (NativeCompiler.wordEqTest encUnary).comp
    (commandOperationsCompiler.pair (NativeCompiler.const eCommandInput encUnary r))
  let operationInRange := NativeCompiler.unaryLtTest.comp
    (commandOperationCompiler.pair (NativeCompiler.const eCommandInput encUnary r))
  let nextInRange := NativeCompiler.unaryLtTest.comp
    (commandNextCompiler.pair commandStatesCompiler)
  exact NativeCompiler.ite countMatches
    (NativeCompiler.ite operationInRange
      (NativeCompiler.ite nextInRange commandQueryWordCompiler commandHaltWordCompiler)
      commandHaltWordCompiler)
    commandHaltWordCompiler

/-- Retained action-constructor dispatch test on the complete command input. -/
noncomputable def ICfg.isQueryCompiler :
    NativeCompiler (fun input : CommandInput => (eAct_toSum input.2.2.2).isRight)
      eCommandInput Turing.MultiTapeTM.encTest :=
  NativeCompiler.boolToTest.comp
    (((NativeCompiler.sumTag eStepPayload eQueryPayload).ofInputEq eAct_toSum fun _ => rfl).comp
      commandActCompiler)

/-- Retained local-command encoding for the ordinary-step branch. -/
noncomputable def ICfg.localCommandWordCompiler :
    NativeCompiler
      (fun input : CommandInput => false :: eICfg
        (input.2.2.1.step input.2.1 input.1.states input.2.2.2.stepPayload.1
          input.2.2.2.stepPayload.2.1 input.2.2.2.stepPayload.2.2))
      eCommandInput Turing.MultiTapeTM.encBits :=
  (NativeCompiler.prefixBit false).comp ICfg.localStepCompiler

/-- Retained exact action interpreter. Constructor dispatch, local execution and validated query
execution remain separately exposed constituent machines for phase-aware accounting. -/
noncomputable def ICfg.commandCompiler (r : ℕ) :
    NativeCompiler
      (fun input : Desc × (List ℕ × (ICfg × Act)) =>
        input.2.2.1.command r input.1 input.2.1 input.2.2.2)
      (encPair eDesc (encPair (encList encUnary) (encPair eICfg eAct))) (eCommand r) := by
  let assembled := NativeCompiler.ite ICfg.isQueryCompiler
    (ICfg.queryCommandWordCompiler r) ICfg.localCommandWordCompiler
  refine assembled.ofOutputEq ?_
  rintro ⟨description, input, cfg, action⟩
  cases action with
  | step ordinary querySymbols answerMoves => rfl
  | query operation next =>
      simp only [ICfg.command]
      split_ifs <;> rfl

/-- Retained selection of one explicitly stored probabilistic branch. -/
noncomputable def Branches.getCompiler :
    NativeCompiler (fun input : Branches × Bool => input.1.get input.2)
      (encPair eBranches encBool) eAct := by
  let branches := NativeCompiler.first eBranches encBool
  let coin := NativeCompiler.second eBranches encBool
  let falseBranch := (NativeCompiler.first eAct eAct).ofInputEq
    (fun branches : Branches => (branches.falseBranch, branches.trueBranch)) fun _ => rfl
  let trueBranch := (NativeCompiler.second eAct eAct).ofInputEq
    (fun branches : Branches => (branches.falseBranch, branches.trueBranch)) fun _ => rfl
  exact NativeCompiler.ite (NativeCompiler.boolToTest.comp coin)
    (trueBranch.comp branches) (falseBranch.comp branches)

/-- Retained active-control key construction on the complete `commandAt` input layout. -/
noncomputable def ICfg.commandAtKeyCompiler :
    NativeCompiler
      (fun input : CommandAtInput =>
        input.2.2.1.key input.2.1 ((input.2.2.1.control.getD none).getD 0))
      eCommandAtInput eKey := by
  let tail := NativeCompiler.second eDesc
    (encPair (encList encUnary) (encPair eICfg encBool))
  let word := (NativeCompiler.first (encList encUnary)
    (encPair eICfg encBool)).comp tail
  let cfgCoin := (NativeCompiler.second (encList encUnary)
    (encPair eICfg encBool)).comp tail
  let cfg := (NativeCompiler.first eICfg encBool).comp cfgCoin
  let control := ICfg.controlCompiler.comp cfg
  let inner := (NativeCompiler.optionGetD none Turing.MultiTapeTM.Universal.eSym).comp control
  let state := (NativeCompiler.optionGetD 0 encUnary).comp inner
  exact ICfg.keyCompiler.comp (word.pair (cfg.pair state))

/-- Retained first-match lookup stage on the complete `commandAt` input layout. -/
noncomputable def ICfg.commandAtLookupCompiler :
    NativeCompiler
      (fun input : CommandAtInput => NativeCompiler.firstMatch (input.1.table,
        input.2.2.1.key input.2.1 ((input.2.2.1.control.getD none).getD 0)))
      eCommandAtInput (encOption eBranches) := by
  let description := NativeCompiler.first eDesc
    (encPair (encList encUnary) (encPair eICfg encBool))
  let table := Desc.tableCompiler.comp description
  exact (NativeCompiler.firstMatchCompiler eKey eBranches).comp
    (table.pair ICfg.commandAtKeyCompiler)

/-- One `commandAt` input paired with its already-computed first-match result. -/
def commandAtFromLookup (r : ℕ) (input : CommandAtLookupInput) : Command r :=
  match input.1.2.2.1.control with
  | none => .local input.1.2.2.1
  | some none => .local input.1.2.2.1.halt
  | some (some _) =>
      match input.2 with
      | none => .local input.1.2.2.1.halt
      | some branches =>
          input.1.2.2.1.command r input.1.1 input.1.2.1 (branches.get input.1.2.2.2)

/-- The source `commandAt` function factors through one captured first-match result. -/
theorem commandAtFromLookup_firstMatch (r : ℕ) (input : CommandAtInput) :
    commandAtFromLookup r (input, NativeCompiler.firstMatch (input.1.table,
      input.2.2.1.key input.2.1 ((input.2.2.1.control.getD none).getD 0))) =
      input.2.2.1.commandAt r input.1 input.2.1 input.2.2.2 := by
  rcases input with ⟨description, input, cfg, coin⟩
  cases hcontrol : cfg.control with
  | none => simp [commandAtFromLookup, ICfg.commandAt, hcontrol]
  | some control =>
      cases control with
      | none => simp [commandAtFromLookup, ICfg.commandAt, hcontrol]
      | some state =>
          simp [commandAtFromLookup, ICfg.commandAt, hcontrol,
            Turing.MultiTapeTM.Internal.NativeCompiler.firstMatch]

/-- Execute key construction and the table scan once, then retain the result beside the original
input for all later tag and coin-dispatch stages. -/
noncomputable def ICfg.commandAtLookupStageCompiler :
    NativeCompiler
      (fun input : CommandAtInput => (input, NativeCompiler.firstMatch (input.1.table,
        input.2.2.1.key input.2.1 ((input.2.2.1.control.getD none).getD 0))))
      eCommandAtInput eCommandAtLookupInput :=
  (NativeCompiler.identity eCommandAtInput).pair ICfg.commandAtLookupCompiler

/-- Retained coin-selection stage consuming a captured lookup result. The inhabited default is
used only behind the separately exposed lookup-presence test. -/
noncomputable def ICfg.commandAtActionCompiler :
    NativeCompiler
      (fun input : CommandAtLookupInput => input.2.getD default |>.get input.1.2.2.2)
      eCommandAtLookupInput eAct := by
  let original := NativeCompiler.first eCommandAtInput (encOption eBranches)
  let lookup := NativeCompiler.second eCommandAtInput (encOption eBranches)
  let originalTail := (NativeCompiler.second eDesc
    (encPair (encList encUnary) (encPair eICfg encBool))).comp original
  let cfgCoin := (NativeCompiler.second (encList encUnary)
    (encPair eICfg encBool)).comp originalTail
  let coin := (NativeCompiler.second eICfg encBool).comp cfgCoin
  let branches := (NativeCompiler.optionGetD default eBranches).comp lookup
  exact Branches.getCompiler.comp (branches.pair coin)

/-- Retained tag/coin/command stages after lookup has been captured. This machine performs no key
construction or table scan. -/
noncomputable def ICfg.commandAtFromLookupCompiler (r : ℕ) :
    NativeCompiler (commandAtFromLookup r) eCommandAtLookupInput (eCommand r) := by
  let original := NativeCompiler.first eCommandAtInput (encOption eBranches)
  let lookup := NativeCompiler.second eCommandAtInput (encOption eBranches)
  let description := (NativeCompiler.first eDesc
    (encPair (encList encUnary) (encPair eICfg encBool))).comp original
  let originalTail := (NativeCompiler.second eDesc
    (encPair (encList encUnary) (encPair eICfg encBool))).comp original
  let word := (NativeCompiler.first (encList encUnary)
    (encPair eICfg encBool)).comp originalTail
  let cfgCoin := (NativeCompiler.second (encList encUnary)
    (encPair eICfg encBool)).comp originalTail
  let cfg := (NativeCompiler.first eICfg encBool).comp cfgCoin
  let control := ICfg.controlCompiler.comp cfg
  let hasControl := (NativeCompiler.optionIsSomeTest Turing.MultiTapeTM.Universal.eSym).comp control
  let inner := (NativeCompiler.optionGetD none Turing.MultiTapeTM.Universal.eSym).comp control
  let hasState := (NativeCompiler.optionIsSomeTest encUnary).comp inner
  let hasEntry := (NativeCompiler.optionIsSomeTest eBranches).comp lookup
  let action := ICfg.commandAtActionCompiler
  let activeCommand := ICfg.commandCompiler r |>.comp
    (description.pair (word.pair (cfg.pair action)))
  let keepWord := (NativeCompiler.prefixBit false).comp cfg
  let haltWord := (NativeCompiler.prefixBit false).comp (ICfg.haltCompiler.comp cfg)
  let active := NativeCompiler.ite hasEntry activeCommand haltWord
  let assembled := NativeCompiler.ite hasControl
    (NativeCompiler.ite hasState active haltWord) keepWord
  refine assembled.ofOutputEq ?_
  rintro ⟨⟨description, input, cfg, coin⟩, lookup⟩
  cases hcontrol : cfg.control with
  | none => simp [commandAtFromLookup, hcontrol]
  | some control =>
      cases control with
      | none => simp [commandAtFromLookup, hcontrol]
      | some state => cases lookup <;> simp [commandAtFromLookup, hcontrol]

/-- Retained complete table/action interpreter with exactly one first-match table scan. The lookup
stage and the post-lookup tag/coin/local-command stage remain separately chargeable. -/
noncomputable def ICfg.commandAtCompiler (r : ℕ) :
    NativeCompiler
      (fun input : Desc × (List ℕ × (ICfg × Bool)) =>
        input.2.2.1.commandAt r input.1 input.2.1 input.2.2.2)
      (encPair eDesc (encPair (encList encUnary) (encPair eICfg encBool))) (eCommand r) :=
  ((ICfg.commandAtFromLookupCompiler r).comp ICfg.commandAtLookupStageCompiler).ofOutputEq
    fun input => congrArg (eCommand r) (commandAtFromLookup_firstMatch r input).symm

/-- Retained initialization of the nested optional control. Invalid initial tags enter the
explicit trap control `some none`. -/
noncomputable def ICfg.initControlCompiler :
    NativeCompiler (fun d : Desc => some ((Fin.ofNat? d.states d.q₀).map Fin.val))
      eDesc (encOption (encOption encUnary)) := by
  let initialAndStates := Desc.initialCompiler.pair Desc.statesCompiler
  let inRange := NativeCompiler.unaryLtTest.comp initialAndStates
  let valid := (NativeCompiler.optionSome encUnary).comp Desc.initialCompiler
  let invalid := NativeCompiler.const eDesc (encOption encUnary) none
  let inner := NativeCompiler.ite inRange valid invalid
  refine ((NativeCompiler.optionSome (encOption encUnary)).comp inner).ofOutputEq ?_
  intro d
  by_cases h : d.q₀ < d.states
  · simp [h, Fin.ofNat?_eq_some_of_lt]
  · simp [h, Fin.ofNat?_eq_none_of_not_lt]

/-- Retained initialization of the blank work-tape list. -/
noncomputable def ICfg.initWorkTapesCompiler :
    NativeCompiler (fun d : Desc => List.replicate d.tapes blankTape)
      eDesc (encList Turing.MultiTapeTM.Universal.eTape) := by
  let blank := NativeCompiler.const eDesc Turing.MultiTapeTM.Universal.eTape blankTape
  exact (NativeCompiler.replicateUnaryCompiler Turing.MultiTapeTM.Universal.eTape).comp
    (blank.pair Desc.tapesCompiler)

/-- Retained initialization of the blank channel list. -/
noncomputable def ICfg.initChannelsCompiler :
    NativeCompiler (fun d : Desc => List.replicate d.operations Channel.blank)
      eDesc (encList eChannel) := by
  let blank := NativeCompiler.const eDesc eChannel Channel.blank
  exact (NativeCompiler.replicateUnaryCompiler eChannel).comp
    (blank.pair Desc.operationsCompiler)

/-- Retained exact initialization from a probabilistic description to first-order storage. -/
noncomputable def ICfg.initCompiler : NativeCompiler ICfg.init eDesc eICfg := by
  let inputPos := NativeCompiler.const eDesc encNat 1
  let output := NativeCompiler.const eDesc (encList encUnary) []
  let fields := ICfg.initControlCompiler.pair
    (inputPos.pair (ICfg.initWorkTapesCompiler.pair
      (output.pair ICfg.initChannelsCompiler)))
  exact fields.ofOutputEq fun _ => rfl

/-- First matching transition-table value, preserving table order. -/
abbrev firstMatch : List (Key × Branches) × Key → Option Branches :=
  NativeCompiler.firstMatch

/-- Retained streaming first-match transition-table lookup. -/
noncomputable def firstMatchCompiler :
    NativeCompiler firstMatch
      (encPair (encList (encPair eKey eBranches)) eKey) (encOption eBranches) :=
  NativeCompiler.firstMatchCompiler eKey eBranches

end Turing.MultiTapePTM.Universal

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.FirstOrder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Probabilistic.Oracle.Iteration
public import CslibFrontier.Computability.Probabilistic.Oracle.Time
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bound
import CslibFrontier.Languages.Probabilistic.QueryCount.Support

/-!
# Fixed-channel oracle interpretation and traffic accounting

This module defines the fixed-channel Boolean word program that interprets
`Turing.MultiTapePTM.Universal.Desc` values. It is indexed only by the finite external channel
count `r`. A runtime description is accepted exactly when its declared operation count is `r`; a
mismatch returns the empty word and makes no external call. Dynamic operation tags are checked
before they become `Fin r` values, so the program never exposes a natural-number callback channel.

The definitions and theorems in this module establish source semantics and traffic bounds. They
do **not** by themselves provide the named finite oracle machine, its static description size, or
its online time and workspace. In particular, functional evaluation of `List.find?`, `encList`,
reply-prefix copying and decoding, finite-channel dispatch, and request/reply marshalling is not a
constant-time machine step and is not a free callback. The retained witness in
`Turing.MultiTapePTM.Universal.NativeInterpreter` implements and charges each of those operations.

Natural-number requests and replies use `encList encUnary` on each Boolean channel. A source run
of `fuel` instructions can observe only `fuel` reply symbols, by
`MultiTapePTM.finiteRunFrom_take_runOracle`. Reading those symbols from a Boolean code has a
separate cost: `RunInput.replyBits` is the maximum prefix copied from each encoded reply. Exact
semantics needs that prefix to contain the encoding of the first `fuel` reply symbols. This is
unavoidable because one natural-number symbol may have arbitrarily long unary code. The external
handler's computation remains outside the interpreter coordinate and must be charged separately
when composing the interpreter with an implementation of that handler, including that handler's
static program, online time, workspace and any further oracle traffic.

A composed native bound must likewise name every actual finite component exactly once: the
adversary or reduction, its controller, the interpreter, each hardwired program or descriptor, and
any generated code. Dynamic state and operation tags do not hide code or dispatch costs. A source
call count alone also does not charge the online work used to marshal and issue a physical call or
to copy and read its reply.

The installed-artifact inventory follows the actual construction: the controller, finite
dispatcher and query primitives are inlined into one retained native interpreter, so that final
interpreter description is installed and charged once. Adding its component descriptions as
separate installed copies would double count them. Component sizes may still be exposed as
nonadditive construction coordinates. A separately installed handler is a distinct inventory
entry. The runtime description supplied in `RunInput` is not an installed artifact in this module.

The resource coordinates proved here are exposed separately: complete runtime input bits, its
non-description clock/input/reply-budget tail, the supplied description's bits, physical fair
coins, source calls and request lengths, encoded request lengths, source reply-prefix symbols and
encoded reply-prefix bits. The supplied description is already a field of `RunInput`, so it is
charged there; adding `suppliedDescSize` to `runInputSize` would double count it. A construction
that instead hardwires the supplied descriptor must move that charge into the generated static
program rather than retain both charges. The fixed interpreter's own static description is a
different coordinate and may depend on `r`; it must include its controller and finite-channel
dispatch code. Native online time and workspace are likewise separate coordinates. No scalar
aggregate is canonical here; any scalar bound must be explicitly defined and proved from the
componentwise bounds.

No offline compiler is executed by `run`. If a later construction uses an offline compiler to
produce the fixed interpreter, the compiler's output size is the interpreter's static-code charge;
the compilation time and workspace stay offline unless a composed program actually executes that
compiler, in which case they must be included in that program's online resources.

## Main definitions

* `Turing.MultiTapePTM.Universal.RunInput`: descriptor, source clock, input and reply-code budget.
* `Turing.MultiTapePTM.Universal.runParameterSize`: the non-description runtime-data coordinate.
* `Turing.MultiTapePTM.Universal.Channel`, `.ICfg`: first-order interpreter storage.
* `Turing.MultiTapePTM.Universal.run`: fixed-`Fin r` Boolean-channel interpretation.
* `Turing.MultiTapePTM.Universal.wordCodec`: unary-list word view of source oracle channels.

## Main results

* `Turing.MultiTapePTM.Universal.runWith_eq_runOracle`: exact joint output/state semantics.
* `Turing.MultiTapePTM.Universal.runWith_input_eq_runOracle`: the same law indexed by the named
  source/encoded reply-prefix coordinates.
* `Turing.MultiTapePTM.Universal.isCostBounded_run_privateCoins`: source fuel bounds private coins.
* `Turing.MultiTapePTM.Universal.isQueryBounded_run`: source fuel bounds physical calls.
* `Turing.MultiTapePTM.Universal.queriesSatisfy_run_requestBounds`: canonical source requests and
  their source-symbol and encoded-bit bounds.
* `Turing.MultiTapePTM.Universal.queriesSatisfy_run_encodedRequestBound`: encoded request bits.
* `Turing.MultiTapePTM.Universal.run_query_bounds`: source fuel bounds calls and request symbols.
* `Turing.MultiTapePTM.Universal.unaryListDecoder_take_encList`: a sufficient reply prefix decodes
  every source reply symbol the instruction clock can observe.

## References

The fixed-channel interpreter and its componentwise accounting are original to this module.
-/

@[expose] public section

namespace Turing.MultiTapePTM.Universal

open Cslib Cslib.Probability Turing.MultiTapeMachine
  Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Runtime input to the fixed interpreter. `fuel` counts source oracle-machine instructions;
`replyBits` separately bounds the Boolean prefix copied from each encoded external reply. -/
structure RunInput where
  /-- Supplied first-order oracle-machine description. -/
  desc : Desc
  /-- Number of source instructions to interpret. -/
  fuel : ℕ
  /-- Source input word. -/
  input : List ℕ
  /-- Maximum Boolean prefix copied from each encoded reply. -/
  replyBits : ℕ

/-- Runtime inputs are encoded in field order, with both numeric budgets in unary. -/
enc_structure eRunInput : RunInput where
  desc : eDesc, fuel : encUnary, input : (encList encUnary), replyBits : encUnary

/-- Encoding of the runtime source clock, source input and reply-copy budget after the separately
framed supplied description. -/
def eRunParameters : (ℕ × (List ℕ × ℕ)) ↪ List Bool :=
  encPair encUnary (encPair (encList encUnary) encUnary)

/-- The supplied descriptor's unary model-code size. This exposes its source/adversary program
size even though the descriptor is runtime data here. Hardwiring it moves this charge into the
generated static program rather than counting it in both coordinates. -/
def suppliedDescSize (i : RunInput) : ℕ := descLen i.desc

/-- The encoded runtime input size. This includes the supplied descriptor, source input, unary
clock and unary reply-code prefix budget exactly once, but not the fixed interpreter code. -/
def runInputSize (i : RunInput) : ℕ := (eRunInput i).length

/-- Exact size of the non-description runtime-data tail: source clock, source input and encoded
reply-prefix budget. This and the framed supplied description partition `eRunInput`; do not add
`suppliedDescSize` to `runInputSize`, which already contains both. -/
def runParameterSize (i : RunInput) : ℕ :=
  (eRunParameters (i.fuel, i.input, i.replyBits)).length

/-- Maximum number of private fair coins: at most one is drawn per source instruction, and halted
storage draws none. -/
def privateCoinBound (i : RunInput) : ℕ := i.fuel

/-- Maximum number of external calls. -/
def queryBound (i : RunInput) : ℕ := i.fuel

/-- Maximum number of source natural-number symbols in one request. -/
def sourceRequestBound (i : RunInput) : ℕ := i.fuel

/-- Maximum unary framed bits in one encoded request. Each request has at most `fuel` symbols, and
every symbol written into a request buffer comes from the supplied description. This is a traffic
size coordinate, not a claim that encoding or copying the request takes constant time. -/
def encodedRequestBound (i : RunInput) : ℕ :=
  i.fuel * (2 * suppliedDescSize i + 1)

/-- Maximum number of source reply symbols that execution can observe from one call. -/
def sourceReplyPrefixBound (i : RunInput) : ℕ := i.fuel

/-- Maximum encoded reply bits copied from one call. This is independent of the source-symbol
prefix because a unary symbol may be arbitrarily large. -/
def encodedReplyPrefixBound (i : RunInput) : ℕ := i.replyBits

/-- A local channel update preserves bounded request symbols when its optional write is bounded. -/
private theorem Channel.requestBound_step {D : ℕ} {channel : Channel}
    (hchannel : ∀ symbol ∈ channel.query, symbol ≤ D) (write : Option ℕ) (move : SignType)
    (hwrite : ∀ symbol, write = some symbol → symbol ≤ D) :
    ∀ symbol ∈ (channel.step write move).query, symbol ≤ D := by
  intro symbol hsymbol
  simp only [Channel.step, List.mem_append, Option.mem_toList] at hsymbol
  rcases hsymbol with hsymbol | hsymbol
  · exact hchannel symbol hsymbol
  · exact hwrite symbol hsymbol

/-- Installing a reply clears the pending request. -/
private theorem Channel.requestBound_receive {D : ℕ} (channel : Channel) (reply : List ℕ) :
    ∀ symbol ∈ (channel.receive reply).query, symbol ≤ D := by
  simp [Channel.receive]

/-- One local instruction grows a channel request by at most one source symbol. -/
private theorem Channel.requestLength_step {steps : ℕ} {channel : Channel}
    (hchannel : channel.query.length ≤ steps) (write : Option ℕ) (move : SignType) :
    (channel.step write move).query.length ≤ steps + 1 := by
  cases write <;> simp only [Channel.step, List.length_append, Option.toList_none,
    Option.toList_some, List.length_nil, List.length_singleton] <;> omega

/-- Installing a reply leaves an empty pending request. -/
private theorem Channel.requestLength_receive (channel : Channel) (reply : List ℕ) (steps : ℕ) :
    (channel.receive reply).query.length ≤ steps := by
  simp [Channel.receive]

/-- Every natural-number symbol accumulated in a request buffer comes from the supplied
description, and is therefore bounded by its encoded length. -/
private def ICfg.RequestBound (d : Desc) (cfg : ICfg) : Prop :=
  cfg.channels.Forall fun channel => ∀ symbol ∈ channel.query, symbol ≤ descLen d

/-- At loop index `steps`, every pending request contains at most `steps` source symbols. -/
private def ICfg.RequestLengthBound (steps : ℕ) (cfg : ICfg) : Prop :=
  cfg.channels.Forall fun channel => channel.query.length ≤ steps

/-- Blank interpreter channels contain no request symbols. -/
private theorem ICfg.requestBound_init (d : Desc) : (ICfg.init d).RequestBound d := by
  simp [ICfg.RequestBound, ICfg.init, Channel.blank]

/-- Blank interpreter channels have zero-length pending requests. -/
private theorem ICfg.requestLengthBound_init (d : Desc) :
    (ICfg.init d).RequestLengthBound 0 := by
  simp [ICfg.RequestLengthBound, ICfg.init, Channel.blank]

/-- Either branch selected from a stored table entry is encoded within the complete supplied
description. -/
private theorem length_selectedAct_le {d : Desc} {entry : Key × Branches}
    (hentry : entry ∈ d.table) (coin : Bool) :
    (eAct (entry.2.get coin)).length ≤ descLen d := by
  have hentryLength := length_le_encList_of_mem (encPair eKey eBranches) hentry
  have htable : (encList (encPair eKey eBranches) d.table).length ≤ descLen d := by
    simp only [descLen, eDesc_apply, length_encPair]
    omega
  have hbranches := length_le_encPair_right eKey eBranches entry
  have hbranch : (eAct (entry.2.get coin)).length ≤ (eBranches entry.2).length := by
    cases coin <;>
      simp only [Branches.get_false, Branches.get_true, eBranches_apply, length_encPair] <;>
      omega
  exact hbranch.trans (hbranches.trans (hentryLength.trans htable))

/-- Every request symbol written by a selected stored action is bounded by the supplied
description's encoded length. -/
private theorem querySymbol_le_descLen {d : Desc} {entry : Key × Branches} {coin : Bool}
    {ordinary : Turing.MultiTapeTM.Universal.Act} {querySymbols : List (Option ℕ)}
    {answerMoves : List SignType} (hentry : entry ∈ d.table)
    (haction : entry.2.get coin = .step ordinary querySymbols answerMoves) :
    ∀ symbol ∈ querySymbols, symbol.getD 0 ≤ descLen d := by
  intro symbol hsymbol
  have hsymbolLength := length_le_encList_of_mem
    Turing.MultiTapeTM.Universal.eSym hsymbol
  have hvalueLength := Turing.MultiTapeTM.Universal.getD_le_length_eSym symbol
  have hactionLength := length_selectedAct_le hentry coin
  rw [haction] at hactionLength
  simp only [eAct_apply, length_encPair, encSum_inl, List.length_cons] at hactionLength
  omega

private theorem List.forall_modify_of {α : Type*} {p : α → Prop} {values : List α}
    (hvalues : values.Forall p) (index : ℕ) (f : α → α)
    (hf : ∀ value, p value → p (f value)) : (values.modify index f).Forall p := by
  induction values generalizing index with
  | nil => simp
  | cons value values ih =>
    cases index with
    | zero =>
      simp only [List.modify, List.forall_cons] at hvalues ⊢
      exact ⟨hf value hvalues.1, hvalues.2⟩
    | succ index =>
      simp only [List.modify, List.forall_cons] at hvalues ⊢
      exact ⟨hvalues.1, ih hvalues.2 index⟩

/-- Local halting leaves every pending request unchanged. -/
private theorem ICfg.RequestBound.halt {d : Desc} {cfg : ICfg} (h : cfg.RequestBound d) :
    cfg.halt.RequestBound d := h

/-- Installing a reply clears one request and preserves the bound on every other channel. -/
private theorem ICfg.RequestBound.receive {d : Desc} {cfg : ICfg} {r : ℕ}
    (h : cfg.RequestBound d) (operation : Fin r) (next : ℕ) (reply : List ℕ) :
    (cfg.receive operation next reply).RequestBound d := by
  unfold ICfg.RequestBound at h ⊢
  simp only [ICfg.receive]
  exact List.forall_modify_of h operation.val (fun _ => Channel.receive reply)
    (fun channel _ => Channel.requestBound_receive channel reply)

/-- A local source step preserves the request-symbol bound when each stored write symbol is
bounded by the supplied description. -/
private theorem ICfg.RequestBound.step {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.RequestBound d) (ordinary : Turing.MultiTapeTM.Universal.Act)
    (querySymbols : List (Option ℕ)) (answerMoves : List SignType)
    (hquerySymbols : ∀ symbol ∈ querySymbols, symbol.getD 0 ≤ descLen d) :
    (cfg.step input d.states ordinary querySymbols answerMoves).RequestBound d := by
  rw [ICfg.RequestBound, List.forall_iff_forall_mem] at h ⊢
  intro channel hchannel
  simp only [ICfg.step] at hchannel
  obtain ⟨index, hindex, rfl⟩ := List.mem_mapIdx.mp hchannel
  refine Channel.requestBound_step (h cfg.channels[index] (List.getElem_mem hindex))
    (querySymbols.getD index none) (answerMoves.getD index 0) ?_
  intro symbol hwrite
  rcases List.getD_mem_or querySymbols index none with hmem | hdefault
  · have hbound := hquerySymbols _ hmem
    simpa only [hwrite, Option.getD_some] using hbound
  · rw [hdefault] at hwrite
    contradiction

/-- A request-length bound is monotone in the step index. -/
private theorem ICfg.RequestLengthBound.mono {steps steps' : ℕ} {cfg : ICfg}
    (h : cfg.RequestLengthBound steps) (hle : steps ≤ steps') :
    cfg.RequestLengthBound steps' := by
  rw [ICfg.RequestLengthBound, List.forall_iff_forall_mem] at h ⊢
  exact fun channel hchannel => (h channel hchannel).trans hle

/-- Local halting preserves pending requests and permits incrementing the loop index. -/
private theorem ICfg.RequestLengthBound.halt {steps : ℕ} {cfg : ICfg}
    (h : cfg.RequestLengthBound steps) : cfg.halt.RequestLengthBound (steps + 1) :=
  h.mono (Nat.le_succ steps)

/-- Installing a reply clears one request and preserves every other request while the loop index
increases. -/
private theorem ICfg.RequestLengthBound.receive {steps : ℕ} {cfg : ICfg} {r : ℕ}
    (h : cfg.RequestLengthBound steps) (operation : Fin r) (next : ℕ) (reply : List ℕ) :
    (cfg.receive operation next reply).RequestLengthBound (steps + 1) := by
  unfold ICfg.RequestLengthBound at h ⊢
  simp only [ICfg.receive]
  exact List.forall_modify_of (List.Forall.imp (fun channel hchannel =>
      hchannel.trans (Nat.le_succ steps)) h) operation.val (fun _ => Channel.receive reply)
    (fun channel _ => Channel.requestLength_receive channel reply (steps + 1))

/-- Every local instruction grows every pending request by at most one symbol. -/
private theorem ICfg.RequestLengthBound.step {d : Desc} {input : List ℕ} {cfg : ICfg}
    {steps : ℕ}
    (h : cfg.RequestLengthBound steps) (ordinary : Turing.MultiTapeTM.Universal.Act)
    (querySymbols : List (Option ℕ)) (answerMoves : List SignType) :
    (cfg.step input d.states ordinary querySymbols answerMoves).RequestLengthBound (steps + 1) := by
  rw [ICfg.RequestLengthBound, List.forall_iff_forall_mem] at h ⊢
  intro channel hchannel
  simp only [ICfg.step] at hchannel
  obtain ⟨index, hindex, rfl⟩ := List.mem_mapIdx.mp hchannel
  exact Channel.requestLength_step (h cfg.channels[index] (List.getElem_mem hindex))
    (querySymbols.getD index none) (answerMoves.getD index 0)

/-- A decoded command preserves bounded request storage; an exposed query additionally carries
only symbols bounded by the supplied description. -/
private def Command.RequestBound (d : Desc) : Command r → Prop
  | .local next => next.RequestBound d
  | .query _ request _ pending =>
      pending.RequestBound d ∧ ∀ symbol ∈ request, symbol ≤ descLen d

/-- A decoded command at loop index `steps` either produces storage bounded at `steps + 1`, or
exposes a request already bounded at `steps`. -/
private def Command.RequestLengthBound (steps : ℕ) : Command r → Prop
  | .local next => next.RequestLengthBound (steps + 1)
  | .query _ request _ pending =>
      pending.RequestLengthBound steps ∧ request.length ≤ steps

/-- A channel read with a default blank record contains only bounded request symbols. -/
private theorem ICfg.RequestBound.getD {d : Desc} {cfg : ICfg}
    (h : cfg.RequestBound d) (index : ℕ) :
    ∀ symbol ∈ (cfg.channels.getD index .blank).query, symbol ≤ descLen d := by
  rw [ICfg.RequestBound, List.forall_iff_forall_mem] at h
  rcases List.getD_mem_or cfg.channels index .blank with hmem | hblank
  · exact h _ hmem
  · rw [hblank]
    simp [Channel.blank]

/-- A channel read with a default blank record inherits the current request-length bound. -/
private theorem ICfg.RequestLengthBound.getD {steps : ℕ} {cfg : ICfg}
    (h : cfg.RequestLengthBound steps) (index : ℕ) :
    (cfg.channels.getD index .blank).query.length ≤ steps := by
  rw [ICfg.RequestLengthBound, List.forall_iff_forall_mem] at h
  rcases List.getD_mem_or cfg.channels index .blank with hmem | hblank
  · exact h _ hmem
  · rw [hblank]
    simp [Channel.blank]

/-- Every decoded command selected from bounded interpreter storage preserves the request-symbol
invariant, and every exposed request satisfies it. -/
private theorem ICfg.commandAt_requestBound {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.RequestBound d) (r : ℕ) (coin : Bool) :
    (cfg.commandAt r d input coin).RequestBound d := by
  cases hcontrol : cfg.control with
  | none => simpa [ICfg.commandAt, hcontrol, Command.RequestBound] using h
  | some control =>
    cases control with
    | none => simpa [ICfg.commandAt, hcontrol, ICfg.command, Command.RequestBound] using h.halt
    | some state =>
      simp only [ICfg.commandAt, hcontrol]
      cases hfind : d.table.find? (fun entry => entry.1 = cfg.key input state) with
      | none => simpa [hfind, Command.RequestBound] using h.halt
      | some entry =>
        have hentry : entry ∈ d.table := List.mem_of_find?_eq_some hfind
        cases haction : entry.2.get coin with
        | step ordinary querySymbols answerMoves =>
          simp only [hfind, haction, ICfg.command, Command.RequestBound]
          exact h.step ordinary querySymbols answerMoves
            (querySymbol_le_descLen hentry haction)
        | query operation next =>
          simp only [hfind, haction, ICfg.command, Command.RequestBound]
          split
          next hcount =>
            split
            next hop =>
              split
              next hnext => exact ⟨h, h.getD operation⟩
              next hnext => exact h.halt
            next hop => exact h.halt
          next hcount => exact h.halt

/-- A decoded command selected at loop index `steps` has the matching request-length bound. -/
private theorem ICfg.commandAt_requestLengthBound {d : Desc} {input : List ℕ} {cfg : ICfg}
    {steps : ℕ} (h : cfg.RequestLengthBound steps) (r : ℕ) (coin : Bool) :
    (cfg.commandAt r d input coin).RequestLengthBound steps := by
  cases hcontrol : cfg.control with
  | none => simpa [ICfg.commandAt, hcontrol, Command.RequestLengthBound] using
      h.mono (Nat.le_succ steps)
  | some control =>
    cases control with
    | none =>
      simpa [ICfg.commandAt, hcontrol, ICfg.command, Command.RequestLengthBound] using h.halt
    | some state =>
      simp only [ICfg.commandAt, hcontrol]
      cases hfind : d.table.find? (fun entry => entry.1 = cfg.key input state) with
      | none => simpa [hfind, Command.RequestLengthBound] using h.halt
      | some entry =>
        cases haction : entry.2.get coin with
        | step ordinary querySymbols answerMoves =>
          simp only [hfind, haction, ICfg.command, Command.RequestLengthBound]
          exact h.step ordinary querySymbols answerMoves
        | query operation next =>
          simp only [hfind, haction, ICfg.command, Command.RequestLengthBound]
          split
          next hcount =>
            split
            next hop =>
              split
              next hnext => exact ⟨h, h.getD operation⟩
              next hnext => exact h.halt
            next hop => exact h.halt
          next hcount => exact h.halt

/-- Proof relation between a decoded first-order command and the selected native action. -/
private inductive CommandCorresponds (d : Desc) (input : List ℕ) (cfg : ICfg) :
    Command d.operations →
      Turing.MultiTapeMachine.Action d.tapes ℕ (Option (Fin d.states))
        (Fin d.operations) → Prop where
  | isLocal (next : ICfg) (ordinary : Turing.Action d.tapes ℕ (Option (Fin d.states)))
      (querySymbols : Fin d.operations → Option ℕ) (answerMoves : Fin d.operations → SignType)
      (hvalid : next.Valid d input)
      (heq : next.toConfig d input =
        (cfg.toConfig d input).step ordinary querySymbols answerMoves) :
      CommandCorresponds d input cfg (.local next) (.step ordinary querySymbols answerMoves)
  | isQuery (operation : Fin d.operations) (request : List ℕ) (next : ℕ)
      (hnext : next < d.states)
      (hrequest : request = ((cfg.toConfig d input).channels operation).queryBuffer) :
      CommandCorresponds d input cfg (.query operation request next cfg)
        (.query operation (some ⟨next, hnext⟩))

/-- Decoding a valid live configuration selects exactly the native description action. -/
private theorem ICfg.commandAt_corresponds {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) {state : ℕ} (hcontrol : cfg.control = some (some state))
    (hstate : state < d.states) (coin : Bool) :
    CommandCorresponds d input cfg (cfg.commandAt d.operations d input coin)
      (d.toMachine.tr (some ⟨state, hstate⟩)
        (cfg.toConfig d input).tapes.inputSymbol
        (cfg.toConfig d input).tapes.workTapeSymbols
        (cfg.toConfig d input).answerSymbols coin) := by
  simp only [Desc.toMachine_tr, Desc.action, ICfg.commandAt, hcontrol]
  rw [← ICfg.key_toConfig h state]
  cases hfind : d.table.find? (fun entry => entry.1 = cfg.key input state) with
  | none =>
    simp only [haltAction]
    exact .isLocal cfg.halt
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }
      (fun _ => none) (fun _ => 0) h.halt (cfg.toConfig_halt h)
  | some entry =>
    simp only
    cases haction : entry.2.get coin with
    | step ordinary querySymbols answerMoves =>
      simp only [ICfg.command, Act.toAction_step]
      exact .isLocal (cfg.step input d.states ordinary querySymbols answerMoves)
        (localAction d.tapes d.states ordinary)
        (fun operation => querySymbols.getD operation.val none)
        (fun operation => answerMoves.getD operation.val 0)
        (h.step ordinary querySymbols answerMoves)
        (cfg.toConfig_step h ordinary querySymbols answerMoves)
    | query operation next =>
      by_cases hop : operation < d.operations
      · by_cases hnext : next < d.states
        · simpa only [ICfg.command, Act.toAction, hop, hnext, dite_true] using
            (CommandCorresponds.isQuery (d := d) (input := input) (cfg := cfg) ⟨operation, hop⟩
              (cfg.channels.getD operation .blank).query next hnext rfl)
        · simpa only [ICfg.command, Act.toAction, haltAction, hop, hnext, dite_true, dite_false]
            using
            (CommandCorresponds.isLocal (d := d) (input := input) (cfg := cfg) cfg.halt
            { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }
            (fun _ => none) (fun _ => 0) h.halt (cfg.toConfig_halt h))
      · simpa only [ICfg.command, Act.toAction, haltAction, hop, dite_true, dite_false] using
          (CommandCorresponds.isLocal (d := d) (input := input) (cfg := cfg) cfg.halt
          { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }
          (fun _ => none) (fun _ => 0) h.halt (cfg.toConfig_halt h))

/-- Execute a decoded typed command, truncating an external reply to the source-symbol budget. -/
noncomputable def runCommand {r : ℕ} (fuel : ℕ) :
    Command r → ProbOracleComp (fun _ : Fin r × List ℕ => List ℕ) ICfg
  | .local next => pure next
  | .query operation request next pending => do
      let reply ← ProbOracleComp.query (operation, request)
      pure (pending.receive operation next (List.take fuel reply))

/-- Running a bounded decoded command preserves the request-symbol invariant for every possible
external reply. -/
private theorem runCommand_requestBound {d : Desc} {r fuel : ℕ} {command : Command r}
    (h : command.RequestBound d) :
    ∀ next ∈ (runCommand fuel command).support, next.RequestBound d := by
  intro result hresult
  cases command with
  | local next =>
    exact (OracleComp.eq_of_mem_supportWith_pure hresult) ▸ h
  | query operation request next pending =>
    obtain ⟨reply, -, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
    exact (OracleComp.eq_of_mem_supportWith_pure hresult) ▸
      h.1.receive operation next (List.take fuel reply)

/-- Running a command selected at loop index `steps` produces request storage bounded at the next
index for every possible external reply. -/
private theorem runCommand_requestLengthBound {r fuel steps : ℕ} {command : Command r}
    (h : command.RequestLengthBound steps) :
    ∀ next ∈ (runCommand fuel command).support, next.RequestLengthBound (steps + 1) := by
  intro result hresult
  cases command with
  | local next =>
    exact (OracleComp.eq_of_mem_supportWith_pure hresult) ▸ h
  | query operation request next pending =>
    obtain ⟨reply, -, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
    exact (OracleComp.eq_of_mem_supportWith_pure hresult) ▸
      h.1.receive operation next (List.take fuel reply)

/-- The decoded and native commands selected by one coin have the same typed program. -/
private theorem ICfg.commandAt_program_eq {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) {state : ℕ} (hcontrol : cfg.control = some (some state))
    (hstate : state < d.states) (coin : Bool) (fuel : ℕ) :
    (do
      let next ← runCommand fuel (cfg.commandAt d.operations d input coin)
      pure (next.toConfig d input)) =
      (match d.toMachine.tr (some ⟨state, hstate⟩)
          (cfg.toConfig d input).tapes.inputSymbol
          (cfg.toConfig d input).tapes.workTapeSymbols
          (cfg.toConfig d input).answerSymbols coin with
      | .step ordinary querySymbols answerMoves =>
          pure ((cfg.toConfig d input).step ordinary querySymbols answerMoves)
      | .query operation next => do
          let reply ← ProbOracleComp.query
            (spec := fun _ : Fin d.operations × List ℕ => List ℕ)
            (operation, ((cfg.toConfig d input).channels operation).queryBuffer)
          pure ((cfg.toConfig d input).receive operation next (List.take fuel reply))) := by
  have hcorr := cfg.commandAt_corresponds h hcontrol hstate coin
  generalize hcommand : cfg.commandAt d.operations d input coin = command at hcorr ⊢
  generalize haction : d.toMachine.tr (some ⟨state, hstate⟩)
      (cfg.toConfig d input).tapes.inputSymbol
      (cfg.toConfig d input).tapes.workTapeSymbols
      (cfg.toConfig d input).answerSymbols coin = action at hcorr ⊢
  cases hcorr with
  | isLocal next ordinary querySymbols answerMoves hvalid heq =>
    simp only [runCommand, pure_bind, heq]
  | isQuery operation request next hnext hrequest =>
    simp only [runCommand, hrequest, bind_assoc, pure_bind,
      ICfg.toConfig_receive h operation hnext]

/-- Typed source-channel execution of one interpreted instruction. Replies are truncated to the
maximum source-symbol prefix that a `fuel`-instruction run can inspect. -/
noncomputable def sourceStep (d : Desc) (input : List ℕ) (fuel : ℕ)
    (cfg : ICfg) :
    ProbOracleComp (fun _ : Fin d.operations × List ℕ => List ℕ) ICfg := do
  match cfg.control with
  | none => pure cfg
  | some _ =>
    let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
    runCommand fuel (cfg.commandAt d.operations d input coin)

/-- A command corresponding to a native action preserves the first-order storage invariant for
every possible oracle reply. -/
private theorem runCommand_valid {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) {command : Command d.operations}
    {action : Turing.MultiTapeMachine.Action d.tapes ℕ (Option (Fin d.states))
      (Fin d.operations)} (hcorr : CommandCorresponds d input cfg command action)
    (fuel : ℕ) :
    ∀ next ∈ (runCommand fuel command).support, next.Valid d input := by
  intro result hresult
  cases hcorr with
  | isLocal next ordinary querySymbols answerMoves hvalid heq =>
    exact (OracleComp.eq_of_mem_supportWith_pure hresult) ▸ hvalid
  | isQuery operation request next hnext hrequest =>
    obtain ⟨reply, -, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
    exact (OracleComp.eq_of_mem_supportWith_pure hresult) ▸
      h.receive operation hnext (List.take fuel reply)

/-- Every possible typed source-channel step preserves valid interpreter storage. -/
theorem ICfg.sourceStep_valid {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) (fuel : ℕ) :
    ∀ next ∈ (sourceStep d input fuel cfg).support, next.Valid d input := by
  intro next hnext
  cases hcontrol : cfg.control with
  | none =>
    have hnext' : next ∈ (pure cfg : ProbOracleComp
        (fun _ : Fin d.operations × List ℕ => List ℕ) ICfg).support := by
      simpa only [sourceStep, hcontrol] using hnext
    exact (OracleComp.eq_of_mem_supportWith_pure hnext') ▸ h
  | some control =>
    have hnext' : next ∈ (ProbOracleComp.sample (ProbComp.uniform Bool) >>= fun coin =>
        runCommand fuel (cfg.commandAt d.operations d input coin)).support := by
      simpa only [sourceStep, hcontrol] using hnext
    obtain ⟨coin, -, hnext'⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext'
    cases control with
    | none =>
      have hresult : next ∈ (pure cfg.halt : ProbOracleComp
          (fun _ : Fin d.operations × List ℕ => List ℕ) ICfg).support := by
        simpa only [ICfg.commandAt, hcontrol, runCommand] using hnext'
      exact (OracleComp.eq_of_mem_supportWith_pure hresult) ▸ h.halt
    | some state =>
      have hstate : state < d.states := h.control state hcontrol
      exact runCommand_valid h (cfg.commandAt_corresponds h hcontrol hstate coin) fuel next hnext'

/-- Every possible typed source-channel step preserves the request-symbol invariant. -/
private theorem ICfg.sourceStep_requestBound {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.RequestBound d) (fuel : ℕ) :
    ∀ next ∈ (sourceStep d input fuel cfg).support, next.RequestBound d := by
  intro next hnext
  cases hcontrol : cfg.control with
  | none =>
    have hnext' : next ∈ (pure cfg : ProbOracleComp
        (fun _ : Fin d.operations × List ℕ => List ℕ) ICfg).support := by
      simpa only [sourceStep, hcontrol] using hnext
    exact (OracleComp.eq_of_mem_supportWith_pure hnext') ▸ h
  | some control =>
    have hnext' : next ∈ (ProbOracleComp.sample (ProbComp.uniform Bool) >>= fun coin =>
        runCommand fuel (cfg.commandAt d.operations d input coin)).support := by
      simpa only [sourceStep, hcontrol] using hnext
    obtain ⟨coin, -, hnext'⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext'
    exact runCommand_requestBound (cfg.commandAt_requestBound h d.operations coin) next hnext'

/-- At loop index `steps`, every possible typed source-channel step preserves the corresponding
request-length invariant at `steps + 1`. -/
private theorem ICfg.sourceStep_requestLengthBound {d : Desc} {input : List ℕ} {cfg : ICfg}
    {steps : ℕ} (h : cfg.RequestLengthBound steps) (fuel : ℕ) :
    ∀ next ∈ (sourceStep d input fuel cfg).support, next.RequestLengthBound (steps + 1) := by
  intro next hnext
  cases hcontrol : cfg.control with
  | none =>
    have hnext' : next ∈ (pure cfg : ProbOracleComp
        (fun _ : Fin d.operations × List ℕ => List ℕ) ICfg).support := by
      simpa only [sourceStep, hcontrol] using hnext
    exact (OracleComp.eq_of_mem_supportWith_pure hnext') ▸ h.mono (Nat.le_succ steps)
  | some control =>
    have hnext' : next ∈ (ProbOracleComp.sample (ProbComp.uniform Bool) >>= fun coin =>
        runCommand fuel (cfg.commandAt d.operations d input coin)).support := by
      simpa only [sourceStep, hcontrol] using hnext
    obtain ⟨coin, -, hnext'⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext'
    exact runCommand_requestLengthBound
      (cfg.commandAt_requestLengthBound h d.operations coin) next hnext'

/-- One typed interpreter step, read as a native configuration, is one native description step
whose external reply is truncated to the source-symbol prefix budget. -/
theorem ICfg.sourceStep_toConfig {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) (fuel : ℕ) :
    (do
      let next ← sourceStep d input fuel cfg
      pure (next.toConfig d input)) =
      d.toMachine.runConfigFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun operation request => List.take fuel <$>
          ProbOracleComp.query (operation, request)) 1 (cfg.toConfig d input) := by
  cases hcontrol : cfg.control with
  | none =>
    have hstate : (cfg.toConfig d input).tapes.state = none := by
      simp only [ICfg.toConfig_state, hcontrol, decodeControl]
    simp only [sourceStep, hcontrol, MultiTapePTM.runConfigFrom,
      MultiTapeMachine.runConfigFrom, hstate, pure_bind]
  | some control =>
    cases control with
    | none =>
      have hstate : (cfg.toConfig d input).tapes.state = some none := by
        simp only [ICfg.toConfig_state, hcontrol, decodeControl]
      simp only [sourceStep, hcontrol, MultiTapePTM.runConfigFrom,
        MultiTapeMachine.runConfigFrom, hstate, bind_assoc, bind_map_left]
      refine congrArg (ProbOracleComp.sample (ProbComp.uniform Bool) >>= ·) (funext fun coin => ?_)
      simp only [ICfg.commandAt, hcontrol, runCommand, pure_bind, Desc.toMachine_tr,
        Desc.action, haltAction]
      exact congrArg
        (fun next => (pure next : ProbOracleComp
          (fun _ : Fin d.operations × List ℕ => List ℕ)
          (Config d.tapes ℕ (Option (Fin d.states)) (Fin d.operations) input)))
        (cfg.toConfig_halt h)
    | some state =>
      have hstate : state < d.states := h.control state hcontrol
      have hcfgstate : (cfg.toConfig d input).tapes.state = some (some ⟨state, hstate⟩) := by
        simp only [ICfg.toConfig_state, hcontrol, decodeControl,
          Fin.ofNat?_eq_some_of_lt d.states state hstate, Option.map_some]
      simp only [sourceStep, hcontrol, MultiTapePTM.runConfigFrom,
        MultiTapeMachine.runConfigFrom, hcfgstate, bind_assoc, bind_map_left]
      refine congrArg (ProbOracleComp.sample (ProbComp.uniform Bool) >>= ·) (funext fun coin => ?_)
      rw [cfg.commandAt_program_eq h hcontrol hstate coin fuel]
      cases d.toMachine.tr (some ⟨state, hstate⟩)
          (cfg.toConfig d input).tapes.inputSymbol
          (cfg.toConfig d input).tapes.workTapeSymbols
          (cfg.toConfig d input).answerSymbols coin <;> rfl

/-- A bounded typed interpreter loop is exactly the native description run whose replies are
truncated to the supplied source-symbol prefix budget. -/
theorem ICfg.sourceIterate_toConfig {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) (replyFuel count : ℕ) :
    (do
      let final ← OracleComp.iterate count (sourceStep d input replyFuel) cfg
      pure (final.toConfig d input)) =
      d.toMachine.runConfigFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun operation request => List.take replyFuel <$>
          ProbOracleComp.query (operation, request)) count (cfg.toConfig d input) := by
  induction count generalizing cfg with
  | zero =>
    simp only [OracleComp.iterate_zero, pure_bind, MultiTapePTM.runConfigFrom,
      MultiTapeMachine.runConfigFrom_zero]
  | succ count ih =>
    rw [OracleComp.iterate_succ_bind]
    simp only [bind_assoc, MultiTapePTM.runConfigFrom]
    rw [show count + 1 = 1 + count by omega, MultiTapeMachine.runConfigFrom_add]
    calc
      (sourceStep d input replyFuel cfg >>= fun middle =>
          (OracleComp.iterate count (sourceStep d input replyFuel) middle >>= fun final =>
            pure (final.toConfig d input))) =
        (sourceStep d input replyFuel cfg >>= fun middle =>
          MultiTapeMachine.runConfigFrom d.toMachine
            (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
            (fun operation request => List.take replyFuel <$>
              ProbOracleComp.query (operation, request)) count (middle.toConfig d input)) := by
          apply OracleComp.bind_congr_on_support
          intro middle hmiddle
          exact ih (cfg.sourceStep_valid h replyFuel middle hmiddle)
      _ = (do
          let native ← (do
            let middle ← sourceStep d input replyFuel cfg
            pure (middle.toConfig d input))
          MultiTapeMachine.runConfigFrom d.toMachine
            (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
            (fun operation request => List.take replyFuel <$>
              ProbOracleComp.query (operation, request)) count native) := by
        simp only [bind_assoc, pure_bind]
      _ = MultiTapeMachine.runConfigFrom d.toMachine
          (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
          (fun operation request => List.take replyFuel <$>
            ProbOracleComp.query (operation, request)) 1 (cfg.toConfig d input) >>=
          MultiTapeMachine.runConfigFrom d.toMachine
            (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
            (fun operation request => List.take replyFuel <$>
              ProbOracleComp.query (operation, request)) count := by
        rw [cfg.sourceStep_toConfig h replyFuel]
        rfl

/-- Typed source-channel execution of a description from blank interpreter storage. -/
noncomputable def sourceRun (d : Desc) (fuel : ℕ) (input : List ℕ) :
    ProbOracleComp (fun _ : Fin d.operations × List ℕ => List ℕ) (List ℕ) := do
  let final ← OracleComp.iterate fuel (sourceStep d input fuel) (ICfg.init d)
  pure final.output

/-- Truncating every source reply to the instruction clock preserves the native open run. -/
private theorem run_take_eq_runOracle (d : Desc) (fuel : ℕ) (input : List ℕ) :
    d.toMachine.run (ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun operation request => List.take fuel <$>
          ProbOracleComp.query (operation, request)) fuel input =
      d.runOracle fuel input := by
  change MultiTapeMachine.run d.toMachine
      (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun operation request => List.take fuel <$> ProbOracleComp.query (operation, request))
      fuel input = d.toMachine.runOracle fuel input
  rw [← MultiTapeMachine.finiteRunFrom_init,
    MultiTapePTM.finiteRunFrom_take_runOracle]

/-- The typed interpreter loop has exactly the original open semantics of the supplied
description. The external handler remains uninterpreted and may keep arbitrary shared state. -/
theorem sourceRun_eq_runOracle (d : Desc) (fuel : ℕ) (input : List ℕ) :
    sourceRun d fuel input = d.runOracle fuel input := by
  have hrun := (ICfg.init d).sourceIterate_toConfig (ICfg.valid_init d input) fuel fuel
  have hout := congrArg
    (fun program => (fun final => final.tapes.output) <$> program) hrun
  have htruncated : sourceRun d fuel input =
      d.toMachine.run (ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun operation request => List.take fuel <$>
          ProbOracleComp.query (operation, request)) fuel input := by
    simpa only [sourceRun, map_bind, map_pure, ICfg.toConfig, ICfg.toConfig_init,
      MultiTapePTM.run, MultiTapePTM.runFrom] using hout
  exact htruncated.trans (run_take_eq_runOracle d fuel input)

/-- Total decoder for unary lists, used for encoded oracle replies. -/
def unaryListDecoder : Turing.MultiTapeTM.Decoder (encList encUnary) :=
  .list .unary

/-- Complete framed list elements remain the initial frames after appending any raw suffix. -/
private theorem frames_encList_append {α : Type} (enc : α ↪ List Bool)
    (values : List α) (suffix : List Bool) :
    frames (encList enc values ++ suffix) = values.map enc ++ frames suffix := by
  induction values with
  | nil => simp only [encList_nil, List.nil_append, List.map_nil, frames_nil]
  | cons value values ih =>
    rw [encList_cons, List.append_assoc, frames_frame_append, ih, List.map_cons,
      List.cons_append]

/-- Copying enough bits to contain the encoding of the first `fuel` reply symbols makes those
symbols decode exactly. Extra copied bits and a final incomplete frame cannot affect the prefix. -/
theorem unaryListDecoder_take_encList (reply : List ℕ) (fuel replyBits : ℕ)
    (hfit : (encList encUnary (reply.take fuel)).length ≤ replyBits) :
    (unaryListDecoder.decode ((encList encUnary reply).take replyBits)).take fuel =
      reply.take fuel := by
  by_cases hshort : reply.length ≤ fuel
  · have htake : reply.take fuel = reply := List.take_of_length_le hshort
    rw [htake] at hfit ⊢
    rw [List.take_of_length_le hfit, unaryListDecoder.decode_enc,
      List.take_of_length_le hshort]
  · have hfuel : fuel ≤ reply.length := Nat.le_of_lt (Nat.lt_of_not_ge hshort)
    have hprefixLength : (reply.take fuel).length = fuel := by
      simp only [List.length_take, Nat.min_eq_left hfuel]
    have henc : encList encUnary reply =
        encList encUnary (reply.take fuel) ++ encList encUnary (reply.drop fuel) := by
      rw [← encList_append, List.take_append_drop]
    change ((frames ((encList encUnary reply).take replyBits)).map
      (fun word => word.length)).take fuel = reply.take fuel
    rw [henc, List.take_append, List.take_of_length_le hfit, frames_encList_append,
      List.map_append, List.map_map]
    simp only [Function.comp_apply, encUnary_apply, List.length_replicate]
    simpa only [hprefixLength] using
      (List.take_append_length (l₁ := reply.take fuel)
        (l₂ := (frames
          ((encList encUnary (reply.drop fuel)).take
            (replyBits - (encList encUnary (reply.take fuel)).length))).map List.length))

/-- Source-level execution of one instruction on fixed Boolean channels. Semantically only
`replyBits` bits of the encoded reply and the first `fuel` decoded source symbols are observed.
The native witness must separately charge prefix copying and decoding; this definition does not
make either operation a constant-time step. Halted configurations consume no further coins. -/
noncomputable def wordStep (r : ℕ) (d : Desc) (input : List ℕ) (fuel replyBits : ℕ)
    (cfg : ICfg) : WordOracleComp (Fin r) ICfg := do
  match cfg.control with
  | none => pure cfg
  | some _ =>
    let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
    match cfg.commandAt r d input coin with
    | .local next => pure next
    | .query operation request next pending => do
        let reply ← ProbOracleComp.query (operation, encList encUnary request)
        let decoded := unaryListDecoder.decode (reply.take replyBits)
        pure (pending.receive operation next (decoded.take fuel))

/-- A source request of bounded length whose symbols come from the description has the declared
framed-unary bit bound. -/
private theorem length_encodedRequest_le {d : Desc} {request : List ℕ} {steps : ℕ}
    (hlength : request.length ≤ steps)
    (hsymbol : ∀ symbol ∈ request, symbol ≤ descLen d) :
    (encList encUnary request).length ≤ steps * (2 * descLen d + 1) := by
  refine (length_encList_le encUnary request (b := descLen d) ?_).trans ?_
  · intro symbol hmem
    simpa only [encUnary_apply, List.length_replicate] using hsymbol symbol hmem
  · exact Nat.mul_le_mul_right (2 * descLen d + 1) hlength

/-- Every possible Boolean interpreter step preserves descriptor-bounded request symbols. -/
private theorem ICfg.wordStep_requestBound {r : ℕ} {d : Desc} {input : List ℕ}
    {fuel replyBits : ℕ} {cfg : ICfg} (h : cfg.RequestBound d) :
    ∀ next ∈ (wordStep r d input fuel replyBits cfg).support, next.RequestBound d := by
  intro result hresult
  cases hcontrol : cfg.control with
  | none =>
    have hpure : result ∈ (pure cfg : WordOracleComp (Fin r) ICfg).support := by
      simpa only [wordStep, hcontrol] using hresult
    exact (OracleComp.eq_of_mem_supportWith_pure hpure) ▸ h
  | some control =>
    have hbind : result ∈ (ProbOracleComp.sample (ProbComp.uniform Bool) >>= fun coin =>
        match cfg.commandAt r d input coin with
        | .local next => pure next
        | .query operation request next pending => do
            let reply ← ProbOracleComp.query (operation, encList encUnary request)
            let decoded := unaryListDecoder.decode (reply.take replyBits)
            pure (pending.receive operation next (decoded.take fuel))).support := by
      simpa only [wordStep, hcontrol] using hresult
    obtain ⟨coin, -, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hbind
    have hcommand := cfg.commandAt_requestBound h r coin
    cases heq : cfg.commandAt r d input coin with
    | local next =>
      have hpure : result ∈ (pure next : WordOracleComp (Fin r) ICfg).support := by
        simpa only [heq] using hresult
      simpa only [heq, Command.RequestBound] at hcommand
      exact (OracleComp.eq_of_mem_supportWith_pure hpure) ▸ hcommand
    | query operation request next pending =>
      simpa only [heq, Command.RequestBound] at hcommand
      obtain ⟨reply, -, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp (by
        simpa only [heq] using hresult)
      exact (OracleComp.eq_of_mem_supportWith_pure hpure) ▸
        hcommand.1.receive operation next
          ((unaryListDecoder.decode (reply.take replyBits)).take fuel)

/-- At loop index `steps`, every possible Boolean interpreter step bounds pending request lengths
at the next index. -/
private theorem ICfg.wordStep_requestLengthBound {r : ℕ} {d : Desc} {input : List ℕ}
    {fuel replyBits steps : ℕ} {cfg : ICfg} (h : cfg.RequestLengthBound steps) :
    ∀ next ∈ (wordStep r d input fuel replyBits cfg).support,
      next.RequestLengthBound (steps + 1) := by
  intro result hresult
  cases hcontrol : cfg.control with
  | none =>
    have hpure : result ∈ (pure cfg : WordOracleComp (Fin r) ICfg).support := by
      simpa only [wordStep, hcontrol] using hresult
    exact (OracleComp.eq_of_mem_supportWith_pure hpure) ▸ h.mono (Nat.le_succ steps)
  | some control =>
    have hbind : result ∈ (ProbOracleComp.sample (ProbComp.uniform Bool) >>= fun coin =>
        match cfg.commandAt r d input coin with
        | .local next => pure next
        | .query operation request next pending => do
            let reply ← ProbOracleComp.query (operation, encList encUnary request)
            let decoded := unaryListDecoder.decode (reply.take replyBits)
            pure (pending.receive operation next (decoded.take fuel))).support := by
      simpa only [wordStep, hcontrol] using hresult
    obtain ⟨coin, -, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hbind
    have hcommand := cfg.commandAt_requestLengthBound h r coin
    cases heq : cfg.commandAt r d input coin with
    | local next =>
      have hpure : result ∈ (pure next : WordOracleComp (Fin r) ICfg).support := by
        simpa only [heq] using hresult
      simpa only [heq, Command.RequestLengthBound] at hcommand
      exact (OracleComp.eq_of_mem_supportWith_pure hpure) ▸ hcommand
    | query operation request next pending =>
      simpa only [heq, Command.RequestLengthBound] at hcommand
      obtain ⟨reply, -, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp (by
        simpa only [heq] using hresult)
      exact (OracleComp.eq_of_mem_supportWith_pure hpure) ▸
        hcommand.1.receive operation next
          ((unaryListDecoder.decode (reply.take replyBits)).take fuel)

/-- One Boolean interpreter step at index `steps ≤ fuel` submits a canonical encoding of at most
`fuel` source symbols and fits the declared encoded-request budget. -/
private theorem wordStep_requestBounds {r : ℕ} {d : Desc} {input : List ℕ}
    {fuel replyBits steps : ℕ} {cfg : ICfg} (hsymbol : cfg.RequestBound d)
    (hlength : cfg.RequestLengthBound steps) (hsteps : steps ≤ fuel) :
    (wordStep r d input fuel replyBits cfg).QueriesSatisfy fun request =>
      ∃ source, request.2 = encList encUnary source ∧ source.length ≤ fuel ∧
        request.2.length ≤ fuel * (2 * descLen d + 1) := by
  cases hcontrol : cfg.control with
  | none =>
    exact OracleComp.QueriesSatisfy.pure cfg
  | some control =>
    simp only [wordStep, hcontrol]
    refine (ProbOracleComp.QueriesSatisfy.sample (ProbComp.uniform Bool)).bind fun coin => ?_
    have hsymbolCommand := cfg.commandAt_requestBound hsymbol r coin
    have hlengthCommand := cfg.commandAt_requestLengthBound hlength r coin
    cases heq : cfg.commandAt r d input coin with
    | local next =>
      exact OracleComp.QueriesSatisfy.pure next
    | query operation request next pending =>
      simp only [heq, Command.RequestBound] at hsymbolCommand
      simp only [heq, Command.RequestLengthBound] at hlengthCommand
      refine (ProbOracleComp.QueriesSatisfy.query ?_).bind fun reply =>
        OracleComp.QueriesSatisfy.pure
          (pending.receive operation next
            ((unaryListDecoder.decode (reply.take replyBits)).take fuel))
      exact ⟨request, rfl, hlengthCommand.2.trans hsteps,
        (length_encodedRequest_le hlengthCommand.2 hsymbolCommand.2).trans
          (Nat.mul_le_mul_right (2 * descLen d + 1) hsteps)⟩

/-- Every request in a suffix of the interpreter loop fits the full-run encoded-request budget. -/
private theorem wordIterate_requestBounds {r : ℕ} {d : Desc} {input : List ℕ}
    {fuel replyBits steps count : ℕ} {cfg : ICfg}
    (hsymbol : cfg.RequestBound d) (hlength : cfg.RequestLengthBound steps)
    (hcount : steps + count ≤ fuel) :
    (OracleComp.iterate count (wordStep r d input fuel replyBits) cfg).QueriesSatisfy
      fun request => ∃ source, request.2 = encList encUnary source ∧ source.length ≤ fuel ∧
        request.2.length ≤ fuel * (2 * descLen d + 1) := by
  induction count generalizing steps cfg with
  | zero => exact OracleComp.QueriesSatisfy.pure cfg
  | succ count ih =>
    rw [OracleComp.iterate_succ_bind]
    have hstep : steps ≤ fuel := by omega
    refine OracleComp.IsCostBounded.bind_on_support
      (wordStep_requestBounds hsymbol hlength hstep) ?_
    intro next hnext
    exact ih (cfg.wordStep_requestBound hsymbol next hnext)
      (cfg.wordStep_requestLengthBound hlength next hnext) (by omega)

/-- Fixed-channel Boolean interpreter word program. A channel-count mismatch is rejected before
sampling a coin or making a call. `Universal.NativeInterpreter.artifact` realizes this program and
supplies the independent static-code, online-time and workspace coordinates. -/
noncomputable def run (r : ℕ) (i : RunInput) : WordOracleComp (Fin r) (List ℕ) :=
  if i.desc.operations = r then
    (fun cfg => cfg.output) <$> OracleComp.iterate i.fuel
      (wordStep r i.desc i.input i.fuel i.replyBits) (ICfg.init i.desc)
  else pure []

/-- A physical request fits both request coordinates when it is the canonical encoding of a
source request of bounded length and its Boolean length fits the encoded budget. -/
def RequestFits {r : ℕ} (i : RunInput) (request : Fin r × List Bool) : Prop :=
  ∃ source, request.2 = encList encUnary source ∧ source.length ≤ sourceRequestBound i ∧
    request.2.length ≤ encodedRequestBound i

/-- Every Boolean request submitted by the word program fits both the source-symbol and encoded-bit
traffic coordinates. This structural theorem does not charge native marshalling time. -/
theorem queriesSatisfy_run_requestBounds (r : ℕ) (i : RunInput) :
    (run r i).QueriesSatisfy (RequestFits i) := by
  by_cases hcount : i.desc.operations = r
  · simp only [run, hcount, ↓reduceIte, OracleComp.queriesSatisfy_map_iff,
      RequestFits, sourceRequestBound, encodedRequestBound, suppliedDescSize]
    exact wordIterate_requestBounds (ICfg.requestBound_init i.desc)
      (ICfg.requestLengthBound_init i.desc) (by omega)
  · simp only [run, hcount, ↓reduceIte]
    exact OracleComp.QueriesSatisfy.pure []

/-- In particular, every physical request fits the encoded-bit request coordinate. -/
theorem queriesSatisfy_run_encodedRequestBound (r : ℕ) (i : RunInput) :
    (run r i).QueriesSatisfy fun request => request.2.length ≤ encodedRequestBound i :=
  (queriesSatisfy_run_requestBounds r i).mono fun _ h => by
    rcases h with ⟨source, hcode, hsource, hbits⟩
    exact hbits

/-- A private uniform Boolean draw costs exactly one sampling query and no external query. -/
private theorem sample_uniform_bool_privateCoinBound {r : ℕ} :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 1) (fun _ : Fin r × List Bool => 0))
      (ProbOracleComp.sample (spec := fun _ : Fin r × List Bool => List Bool)
        (ProbComp.uniform Bool)) 1 := by
  rw [ProbComp.uniform, ProbOracleComp.sample_map,
    OracleComp.isCostBounded_map_iff, ProbOracleComp.sample_unifFin]
  exact OracleComp.IsCostBounded.query _

/-- One interpreter instruction consumes at most one private fair coin. Calls to the external
handler have zero private-coin cost. -/
private theorem wordStep_privateCoinBound (r : ℕ) (d : Desc) (input : List ℕ)
    (fuel replyBits : ℕ) (cfg : ICfg) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 1) (fun _ : Fin r × List Bool => 0))
      (wordStep r d input fuel replyBits cfg) 1 := by
  cases hcontrol : cfg.control with
  | none =>
    exact OracleComp.IsCostBounded.pure cfg 1
  | some control =>
    simp only [wordStep, hcontrol]
    refine sample_uniform_bool_privateCoinBound.bind fun coin => ?_
    cases hcommand : cfg.commandAt r d input coin with
    | local next =>
      exact OracleComp.IsCostBounded.pure next 0
    | query operation request next pending =>
      exact (ProbOracleComp.isCostBounded_query (fun _ => 0)
        (operation, encList encUnary request)).bind fun reply =>
          OracleComp.IsCostBounded.pure
            (pending.receive operation next
              ((unaryListDecoder.decode (reply.take replyBits)).take fuel)) 0

/-- One interpreter instruction makes at most one external call. Private sampling is free in this
coordinate. -/
private theorem wordStep_queryBound (r : ℕ) (d : Desc) (input : List ℕ)
    (fuel replyBits : ℕ) (cfg : ICfg) :
    (wordStep r d input fuel replyBits cfg).IsQueryBounded 1 := by
  cases hcontrol : cfg.control with
  | none => exact OracleComp.IsCostBounded.pure cfg 1
  | some control =>
    simp only [wordStep, hcontrol]
    refine (ProbOracleComp.IsQueryBounded.sample (ProbComp.uniform Bool)).bind fun coin => ?_
    cases hcommand : cfg.commandAt r d input coin with
    | local next => exact OracleComp.IsCostBounded.pure next 1
    | query operation request next pending =>
      exact (ProbOracleComp.IsQueryBounded.query
        (operation, encList encUnary request)).bind fun reply =>
          OracleComp.IsCostBounded.pure
            (pending.receive operation next
              ((unaryListDecoder.decode (reply.take replyBits)).take fuel)) 0

/-- A bounded interpreter loop consumes at most one private fair coin per source instruction. -/
theorem isCostBounded_run_privateCoins (r : ℕ) (i : RunInput) :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 1) (fun _ : Fin r × List Bool => 0))
      (run r i) (privateCoinBound i) := by
  by_cases hcount : i.desc.operations = r
  · simp only [run, hcount, ↓reduceIte, privateCoinBound,
      OracleComp.isCostBounded_map_iff]
    have loopBound (count : ℕ) (cfg : ICfg) :
        OracleComp.IsCostBounded
          (Sum.elim (fun _ => 1) (fun _ : Fin r × List Bool => 0))
          (OracleComp.iterate count
            (wordStep r i.desc i.input i.fuel i.replyBits) cfg) count := by
      induction count generalizing cfg with
      | zero => exact OracleComp.IsCostBounded.pure cfg 0
      | succ count ih =>
        rw [OracleComp.iterate_succ_bind]
        exact ((wordStep_privateCoinBound r i.desc i.input i.fuel i.replyBits cfg).bind
          fun next => ih next).mono (by omega)
    exact loopBound i.fuel (ICfg.init i.desc)
  · simp only [run, hcount, ↓reduceIte, privateCoinBound]
    exact OracleComp.IsCostBounded.pure [] i.fuel

/-- The fixed-channel interpreter makes at most one external call per source instruction. -/
theorem isQueryBounded_run (r : ℕ) (i : RunInput) :
    (run r i).IsQueryBounded (queryBound i) := by
  by_cases hcount : i.desc.operations = r
  · simp only [run, hcount, ↓reduceIte, queryBound,
      OracleComp.isCostBounded_map_iff]
    have loopBound (count : ℕ) (cfg : ICfg) :
        (OracleComp.iterate count
          (wordStep r i.desc i.input i.fuel i.replyBits) cfg).IsQueryBounded count := by
      induction count generalizing cfg with
      | zero => exact OracleComp.IsCostBounded.pure cfg 0
      | succ count ih =>
        rw [OracleComp.iterate_succ_bind]
        exact ((wordStep_queryBound r i.desc i.input i.fuel i.replyBits cfg).bind
          fun next => ih next).mono (by omega)
    exact loopBound i.fuel (ICfg.init i.desc)
  · simp only [run, hcount, ↓reduceIte, queryBound]
    exact OracleComp.IsCostBounded.pure [] i.fuel

/-- A channel-count mismatch is rejected without a coin or external call. -/
theorem run_of_operations_ne (r : ℕ) (i : RunInput) (h : i.desc.operations ≠ r) :
    run r i = pure [] := by
  simp only [run, h, ↓reduceIte]

/-- A zero instruction clock returns the empty output, including on a channel-count mismatch. -/
@[simp] theorem run_zero (r : ℕ) (d : Desc) (input : List ℕ) (replyBits : ℕ) :
    run r ⟨d, 0, input, replyBits⟩ = pure [] := by
  by_cases h : d.operations = r
  · simp only [run, h, ↓reduceIte, OracleComp.iterate_zero, map_pure, ICfg.init]
  · exact run_of_operations_ne r ⟨d, 0, input, replyBits⟩ h

/-- Source requests and replies as framed unary lists on the same fixed finite channels. Malformed
request words are not source queries; a word oracle answers them with `[]` without a typed call. -/
def wordCodec (r : ℕ) : OracleCodec (Fin r) (Fin r × List ℕ) fun _ => List ℕ where
  encodeQuery query := (query.1, encList encUnary query.2)
  decodeQuery request :=
    let decoded := unaryListDecoder.decode request.2
    if encList encUnary decoded = request.2 then some (request.1, decoded) else none
  decodeQuery_eq_some_iff request query := by
    let decoded := unaryListDecoder.decode request.2
    change (if encList encUnary decoded = request.2 then some (request.1, decoded) else none) =
        some query ↔ (query.1, encList encUnary query.2) = request
    by_cases hcode : encList encUnary decoded = request.2
    · simp only [hcode, ↓reduceIte]
      constructor
      · intro h
        have hp : (request.1, decoded) = query := Option.some.inj h
        rw [← hp]
        exact Prod.ext rfl hcode
      · intro h
        have hop : query.1 = request.1 := congrArg Prod.fst h
        have hword : encList encUnary query.2 = request.2 := congrArg Prod.snd h
        have hdecoded : decoded = query.2 :=
          (encList encUnary).injective (hcode.trans hword.symm)
        exact congrArg some (Prod.ext hop.symm hdecoded)
    · simp only [hcode, ↓reduceIte]
      constructor
      · intro h
        cases h
      · intro h
        exfalso
        apply hcode
        have hword : encList encUnary query.2 = request.2 := congrArg Prod.snd h
        have hdecoded : decoded = query.2 := by
          dsimp only [decoded]
          rw [← hword, Turing.MultiTapeTM.Decoder.decode_enc]
        rw [hdecoded, hword]
  encodeReply _ := encList encUnary

/-- A malformed request word is answered locally by the codec and makes no typed source call. -/
theorem wordCodec_wordOracle_of_malformed {r : ℕ} {m : Type → Type} [Monad m]
    (handler : Fin r × List ℕ → m (List ℕ)) (request : Fin r × List Bool)
    (h : (wordCodec r).decodeQuery request = none) :
    (wordCodec r).wordOracle handler request = pure [] :=
  OracleCodec.wordOracle_of_decodeQuery_eq_none (wordCodec r) handler h

/-- A stateful source handler's replies fit the Boolean prefix copied by the interpreter. The
condition concerns only replies that the handler can actually return, and it keeps adaptive shared
state fully visible. -/
def ReplyPrefixFits {r : ℕ} {State : Type}
    (handler : Fin r × List ℕ → StateT State PMF (List ℕ))
    (fuel replyBits : ℕ) : Prop :=
  ∀ query state reply nextState,
    (reply, nextState) ∈ (handler query state).support →
      (encList encUnary (reply.take fuel)).length ≤ replyBits

/-- One encoded request/reply exchange agrees with the typed source exchange whenever the copied
Boolean prefix contains every source reply symbol that the clocked run can observe. -/
private theorem runWith_wordQuery_eq_sourceQuery {r : ℕ} {State : Type}
    (handler : Fin r × List ℕ → StateT State PMF (List ℕ))
    {fuel replyBits : ℕ} (hfit : ReplyPrefixFits handler fuel replyBits)
    (operation : Fin r) (request : List ℕ) (next : ℕ) (pending : ICfg) (state : State) :
    ProbOracleComp.runWith ((wordCodec r).wordOracle handler)
        (do
          let reply ← ProbOracleComp.query (operation, encList encUnary request)
          let decoded := unaryListDecoder.decode (reply.take replyBits)
          pure (pending.receive operation next (decoded.take fuel))) state =
      ProbOracleComp.runWith handler
        (do
          let reply ← ProbOracleComp.query (operation, request)
          pure (pending.receive operation next (reply.take fuel))) state := by
  simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
    ProbOracleComp.runWith_pure]
  rw [show (operation, encList encUnary request) =
    (wordCodec r).encodeQuery (operation, request) from rfl,
    OracleCodec.wordOracle_encodeQuery]
  simp only [StateT.run_map, PMF.bind_map, Function.comp_apply]
  apply PMF.bind_congr_on_support
  rintro ⟨reply, nextState⟩ hreply
  rw [unaryListDecoder_take_encList reply fuel replyBits
    (hfit (operation, request) state reply nextState hreply)]

/-- One fixed-channel Boolean interpreter step has the same complete output/private-state law as
the typed source step. This theorem includes halted and malformed local states; neither makes an
external call. -/
theorem runWith_wordStep_eq_sourceStep {State : Type}
    (d : Desc)
    (handler : Fin d.operations × List ℕ → StateT State PMF (List ℕ))
    {fuel replyBits : ℕ} (hfit : ReplyPrefixFits handler fuel replyBits)
    (input : List ℕ) (cfg : ICfg) (state : State) :
    ProbOracleComp.runWith ((wordCodec d.operations).wordOracle handler)
        (wordStep d.operations d input fuel replyBits cfg) state =
      ProbOracleComp.runWith handler (sourceStep d input fuel cfg) state := by
  cases hcontrol : cfg.control with
  | none =>
    simp only [wordStep, sourceStep, hcontrol, ProbOracleComp.runWith_pure]
  | some control =>
    simp only [wordStep, sourceStep, hcontrol, ProbOracleComp.runWith_sample_bind]
    apply PMF.bind_congr_on_support
    intro coin _
    cases hcommand : cfg.commandAt d.operations d input coin with
    | local next =>
      simp only [hcommand, runCommand, ProbOracleComp.runWith_pure]
    | query operation request next pending =>
      simpa only [hcommand, runCommand] using
        runWith_wordQuery_eq_sourceQuery handler hfit operation request next pending state

/-- The encoded and typed interpreter loops have identical adaptive stateful semantics. -/
theorem runWith_wordIterate_eq_sourceIterate {State : Type}
    (d : Desc)
    (handler : Fin d.operations × List ℕ → StateT State PMF (List ℕ))
    {fuel replyBits : ℕ} (hfit : ReplyPrefixFits handler fuel replyBits)
    (input : List ℕ) (count : ℕ) (cfg : ICfg) (state : State) :
    ProbOracleComp.runWith ((wordCodec d.operations).wordOracle handler)
        (OracleComp.iterate count (wordStep d.operations d input fuel replyBits) cfg) state =
      ProbOracleComp.runWith handler
        (OracleComp.iterate count (sourceStep d input fuel) cfg) state := by
  induction count generalizing cfg state with
  | zero => simp only [OracleComp.iterate_zero, ProbOracleComp.runWith_pure]
  | succ count ih =>
    rw [OracleComp.iterate_succ_bind, OracleComp.iterate_succ_bind,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_bind,
      runWith_wordStep_eq_sourceStep d handler hfit input cfg state]
    apply PMF.bind_congr_on_support
    rintro ⟨next, nextState⟩ -
    exact ih next nextState

/-- **Exact fixed-channel open semantics.** Against every adaptive shared-state handler whose
encoded replies fit the declared copied prefix, adapting the Boolean interpreter through
`wordCodec` gives exactly `Desc.runOracle`, including the final handler state. -/
theorem runWith_eq_runOracle {State : Type}
    (d : Desc) (handler : Fin d.operations × List ℕ → StateT State PMF (List ℕ))
    (fuel replyBits : ℕ) (input : List ℕ) (state : State)
    (hfit : ReplyPrefixFits handler fuel replyBits) :
    ProbOracleComp.runWith handler
        ((wordCodec d.operations).adapt
          (run d.operations ⟨d, fuel, input, replyBits⟩)) state =
      ProbOracleComp.runWith handler (d.runOracle fuel input) state := by
  rw [OracleCodec.runWith_adapt]
  calc
    ProbOracleComp.runWith ((wordCodec d.operations).wordOracle handler)
        (run d.operations ⟨d, fuel, input, replyBits⟩) state =
      ProbOracleComp.runWith handler (sourceRun d fuel input) state := by
        simp only [run, ↓reduceIte, ProbOracleComp.runWith_map, sourceRun]
        rw [runWith_wordIterate_eq_sourceIterate d handler hfit input fuel (ICfg.init d) state]
    _ = ProbOracleComp.runWith handler (d.runOracle fuel input) state :=
      congrArg (fun program => ProbOracleComp.runWith handler program state)
        (sourceRun_eq_runOracle d fuel input)

/-- The declared source-symbol and encoded-bit reply-prefix coordinates suffice for every reply
that a stateful handler can actually return. -/
def ReplyBoundsFit {State : Type} (i : RunInput)
    (handler : Fin i.desc.operations × List ℕ → StateT State PMF (List ℕ)) : Prop :=
  ReplyPrefixFits handler (sourceReplyPrefixBound i) (encodedReplyPrefixBound i)

/-- Input-indexed form of exact fixed-channel semantics. It names both reply-prefix coordinates
and keeps the handler's final state visible. -/
theorem runWith_input_eq_runOracle {State : Type} (i : RunInput)
    (handler : Fin i.desc.operations × List ℕ → StateT State PMF (List ℕ)) (state : State)
    (hfit : ReplyBoundsFit i handler) :
    ProbOracleComp.runWith handler
        ((wordCodec i.desc.operations).adapt (run i.desc.operations i)) state =
      ProbOracleComp.runWith handler (i.desc.runOracle i.fuel i.input) state := by
  exact runWith_eq_runOracle i.desc handler i.fuel i.replyBits i.input state hfit

/-- The source clock bounds the number of calls and every request length. Through
`runWith_eq_runOracle`, these are the typed call/request coordinates of every exact interpreter
execution; private coins and encoded request bits are accounted separately. -/
theorem run_query_bounds (d : Desc) (fuel : ℕ) (input : List ℕ) :
    (d.runOracle fuel input).IsQueryBounded fuel ∧
      (d.runOracle fuel input).QueriesSatisfy fun request => request.2.length ≤ fuel := by
  exact MultiTapePTM.query_bounds_runOracle d.toMachine fuel input

end Turing.MultiTapePTM.Universal

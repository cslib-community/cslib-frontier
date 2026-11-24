/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.FrameMachines
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelAppend
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelComp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelZeroSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bound
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Correct
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Logic.Equiv.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Named native compiler witnesses

This internal module retains actual deterministic machine terms through a small construction
kernel. `NativeCompiler` is data, not a second computability predicate: it packages a finite-state
machine, its state encoding, independent time and workspace maps, and a tidy computation proof.
`NativeCompiler.computesInTimeAndSpace` exposes the recorded machine to plain consumers, while
`NativeCompiler.computableInTimeAndSpace` forgets it into the existing existential predicate.

The resource coordinates stay componentwise. `NativeCompiler.staticBits` is the exact encoded
length of the compiler machine; `NativeCompiler.inputBits` and `NativeCompiler.outputBits` are the
exact encoded source and emitted-result lengths; `time` and `workspace` apply only when that
machine is executed.
In particular, using a precompiled result does not pay compiler runtime, but a result used as code
still carries its `outputBits` program-size charge. No scalar total is built into this kernel.
Each coordinate counts one concrete artifact occurrence: a separately stored copy must be charged
again by the enclosing certificate. Thus a payload hardwired into the compiler description and a
copy emitted as output are distinct artifacts, not double counting. The constructor clocks charge
their actual copying, framing, rewinding and intermediate marshalling; they provide no free scan of
an encoded program through finite control.

The constructors use the existing machine combinators directly. In particular, they do not select
a machine from `ComputableInPolyTime`, `ComputableInO`, `ComputableInDegree`, or a normal-form
existence theorem. Their resource formulas retain the constants of those combinators. The exact
static program charge is `NativeCompiler.staticBits`, the `eDesc` length of the packaged machine
under its recorded state encoding.

The constructors assemble fixed machine terms at the proof level; they are not a free dynamic code
generator. The functions and encodings in their types specify behavior and resource expressions,
not callbacks executed outside the packaged machine. A compiler that receives descriptions at
runtime must itself be a `NativeCompiler` whose machine performs that encoded transformation.
Oracle handlers, query/service implementations and universal interpretation are not coordinates of
this deterministic kernel and must be added separately by constructions that use them.

This is a bounded internal prerequisite for concrete compilers. It does not claim that an arbitrary
existential computability proof can be extracted into a `NativeCompiler`.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler`: a named native machine and resource certificate.
* `Turing.MultiTapeTM.Internal.NativeCompiler.staticBits`: exact encoded compiler-machine length.
* `Turing.MultiTapeTM.Internal.NativeCompiler.stateBound`: numeric range of the recorded state
  encoding, computed from its actual codes rather than from state cardinality.
* `Turing.MultiTapeTM.Internal.NativeCompiler.transducerMachineStateEncoding`: constructive
  encoding of the full control state produced by `Transducer.toTM`.
* `Turing.MultiTapeTM.Internal.NativeCompiler.inputBits`: exact encoded input length.
* `Turing.MultiTapeTM.Internal.NativeCompiler.outputBits`: exact encoded output length.
* `Turing.MultiTapeTM.Internal.NativeCompiler.identity`: the copy-and-rewind machine.
* `Turing.MultiTapeTM.Internal.NativeCompiler.const`: a named constant-output machine.
* `Turing.MultiTapeTM.Internal.NativeCompiler.ofInputEq`, `.ofOutputEq`: zero-runtime semantic
  retyping when the actual input or output words agree.
* `Turing.MultiTapeTM.Internal.NativeCompiler.comp`: direct machine composition.
* `Turing.MultiTapeTM.Internal.NativeCompiler.append`: direct raw-word output concatenation.
* `Turing.MultiTapeTM.Internal.NativeCompiler.pair`: direct standard-pair construction.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.description_holds`: the recorded description
  contains every transition of the packaged machine under its recorded encodings.
* `Turing.MultiTapeTM.Internal.NativeCompiler.computableInTimeAndSpace`: forget the named
  construction into the existing plain existential calculus.
-/

public section

namespace Turing.MultiTapeTM.Internal

open Universal

/-- A named finite-state native machine computing `f`, with independent exact-form resource maps.
This is internal construction data, not a parallel public computability calculus. -/
structure NativeCompiler {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) where
  /-- Number of work tapes of the named machine. -/
  tapeCount : ℕ
  /-- Finite control-state type of the named machine. -/
  State : Type
  /-- The control-state type is explicitly finite. -/
  [stateFintype : Fintype State]
  /-- The actual explicit transition table. -/
  table : MultiTapeMachine tapeCount Bool State Empty Id
  /-- State encoding used for the exact universal description. -/
  stateEncoding : State ↪ ℕ
  /-- Native time bound when this machine is executed, kept separate from workspace. -/
  time : α → ℕ
  /-- Native workspace bound when this machine is executed, kept separate from time. -/
  workspace : α → ℕ
  /-- Direct tidy computation certificate for the named machine. -/
  computes : ∀ a, table.toTM.ComputesTidilyInTimeAndSpace (encIn a) (encOut (f a))
    (time a) (workspace a)

namespace NativeCompiler

/-- Constructive disjoint-union encoding used by the core constructors. -/
@[expose] def sumStateEncoding {S₁ S₂ : Type} (left : S₁ ↪ ℕ) (right : S₂ ↪ ℕ) :
    S₁ ⊕ S₂ ↪ ℕ :=
  (left.sumMap right).trans Equiv.natSumNatEquivNat.toEmbedding

/-- Constructive product encoding used by the core constructors. -/
@[expose] def prodStateEncoding {S₁ S₂ : Type} (left : S₁ ↪ ℕ) (right : S₂ ↪ ℕ) :
    S₁ × S₂ ↪ ℕ :=
  (left.prodMap right).trans Nat.pairEquiv.toEmbedding

/-- Constructive optional-state encoding used by the core constructors. -/
@[expose] def optionStateEncoding {S : Type} (state : S ↪ ℕ) : Option S ↪ ℕ :=
  (Equiv.optionEquivSumPUnit S).toEmbedding.trans
    (sumStateEncoding state (Function.Embedding.punit 0))

/-- Constructive encoding of the transducer machine's source state, pending output bit and
end-of-input flag. -/
@[expose] def transducerMachineStateEncoding {State : Type}
    (stateEncoding : State ↪ ℕ) : State × Option Bool × Bool ↪ ℕ :=
  prodStateEncoding stateEncoding
    (prodStateEncoding (optionStateEncoding eBit) eBit)

/-- The unique unit state is encoded as zero. -/
@[expose] def unitStateEncoding : Unit ↪ ℕ :=
  ⟨fun _ => 0, by intro a b _; cases a; cases b; rfl⟩

/-- Explicit encoding of the input-rewinding states. -/
@[expose] def rewindStateEncoding : RewindState ↪ ℕ :=
  ⟨fun q => match q with | .start => 0 | .walk => 1,
    by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- Explicit encoding of the work-tape-rewinding states. -/
@[expose] def rewindWorkStateEncoding : RewindWorkState ↪ ℕ :=
  ⟨fun q => match q with | .start => 0 | .scan => 1,
    by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- Explicit encoding of the work-tape-marking states. -/
@[expose] def markWorkStateEncoding : MarkWorkState ↪ ℕ :=
  ⟨fun q => match q with | .start => 0 | .put => 1,
    by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- One past the largest code that a state numbering assigns. This bounds the codes in use; it is
not the cardinality of the state type. -/
@[expose] def stateEncodingBound {State : Type} [Fintype State] (stateEncoding : State ↪ ℕ) : ℕ :=
  Finset.univ.sup (fun state => stateEncoding state) + 1

/-- Every state code lies strictly below `stateEncodingBound`. -/
theorem stateEncoding_lt_stateEncodingBound {State : Type} [Fintype State]
    (stateEncoding : State ↪ ℕ) (state : State) :
    stateEncoding state < stateEncodingBound stateEncoding :=
  Nat.lt_succ_of_le
    (Finset.le_sup (f := fun state => stateEncoding state) (Finset.mem_univ state))

private def descriptionSymbolCode : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

private theorem descriptionSymbolCode_injective : Function.Injective descriptionSymbolCode := by
  rintro (_ | (_ | _)) (_ | (_ | _)) h <;> simp_all [descriptionSymbolCode]

private def descriptionOrderKey {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (compiler : NativeCompiler f encIn encOut)
    (entry : compiler.State × Option Bool × (Fin compiler.tapeCount → Option Bool)) : List ℕ :=
  compiler.stateEncoding entry.1 :: descriptionSymbolCode entry.2.1 ::
    (List.ofFn entry.2.2).map descriptionSymbolCode

private theorem descriptionOrderKey_injective {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (compiler : NativeCompiler f encIn encOut) :
    Function.Injective (descriptionOrderKey compiler) := by
  rintro ⟨state, input, work⟩ ⟨state', input', work'⟩ h
  simp only [descriptionOrderKey, List.cons.injEq] at h
  rw [compiler.stateEncoding.injective h.1, descriptionSymbolCode_injective h.2.1,
    List.ofFn_injective ((List.map_injective_iff.mpr descriptionSymbolCode_injective) h.2.2)]

@[instance_reducible] private def descriptionEntryOrder {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (compiler : NativeCompiler f encIn encOut) :
    LinearOrder (compiler.State × Option Bool × (Fin compiler.tapeCount → Option Bool)) :=
  LinearOrder.lift' (descriptionOrderKey compiler) (descriptionOrderKey_injective compiler)

/-- The exact universal description obtained by enumerating the retained transition table. -/
def description {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (compiler : NativeCompiler f encIn encOut) : Desc :=
  letI := compiler.stateFintype
  letI := descriptionEntryOrder compiler
  ⟨compiler.tapeCount, compiler.stateEncoding compiler.table.initial,
    (Finset.univ : Finset
      (compiler.State × Option Bool × (Fin compiler.tapeCount → Option Bool))).sort (· ≤ ·) |>.map
      fun ⟨state, input, work⟩ =>
        let action := MultiTapeMachine.Action.emptyOracleEquiv
          (compiler.table.tr state input work Empty.elim)
        (key (compiler.stateEncoding state) (input.map eBit)
          (Option.map eBit ∘ work),
          Act.ofAction (action.map compiler.stateEncoding eBit))⟩

/-- The recorded description contains the packaged table's transition at every state and choice
of symbols under the recorded state and symbol encodings. -/
theorem description_holds {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (compiler : NativeCompiler f encIn encOut)
    (state : compiler.State) (input : Option Bool)
    (work : Fin compiler.tapeCount → Option Bool) :
    compiler.description.Holds (compiler.table.toTM.map compiler.stateEncoding eBit)
      (compiler.stateEncoding state) (input.map eBit) (Option.map eBit ∘ work) := by
  have hmem : (key (compiler.stateEncoding state) (input.map eBit)
      (Option.map eBit ∘ work),
      Act.ofAction ((compiler.table.toTM.tr state input work).map compiler.stateEncoding eBit)) ∈
      compiler.description.table := by
    rw [description]
    refine List.mem_map.mpr ⟨(state, input, work), ?_, ?_⟩
    · simp only [Finset.mem_sort, Finset.mem_univ]
    · simp only [MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
  obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp ((List.find?_isSome
    (p := fun entry => decide (entry.1 = key (compiler.stateEncoding state)
      (input.map eBit) (Option.map eBit ∘ work)))).mpr ⟨_, hmem, by simp⟩)
  have hentry' := hentry
  rw [description] at hentry'
  obtain ⟨⟨state', input', work'⟩, -, rfl⟩ :=
    List.mem_map.mp (List.mem_of_find?_eq_some hentry')
  have hkey := List.find?_some hentry
  simp only [decide_eq_true_eq] at hkey
  cases key_injective compiler.stateEncoding eBit
    (a₁ := (state', input', work')) (a₂ := (state, input, work)) hkey
  rw [Desc.holds_iff]
  simp [hentry, tr_map, MultiTapeMachine.toTM]

/-- Exact length of the compiler input under its recorded encoding. This is a separate resource
coordinate, not runtime charged merely for presenting an already encoded input. -/
@[expose] def inputBits {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (_compiler : NativeCompiler f encIn encOut) (a : α) : ℕ :=
  (encIn a).length

/-- Exact length of the compiler output under its recorded encoding. When the output is executable
code, this is its emitted program-size charge even if compilation itself is offline. -/
@[expose] def outputBits {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (_compiler : NativeCompiler f encIn encOut) (a : α) : ℕ :=
  (encOut (f a)).length

/-- Exact unary-model static program length of the named machine. -/
@[expose] def staticBits {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (compiler : NativeCompiler f encIn encOut) : ℕ :=
  descLen compiler.description

/-- `stateEncodingBound` of the recorded control-state encoding. -/
@[expose] def stateBound {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (compiler : NativeCompiler f encIn encOut) : ℕ :=
  letI := compiler.stateFintype
  stateEncodingBound compiler.stateEncoding

/-- Every recorded state code lies strictly below `stateBound`. -/
theorem stateEncoding_lt_stateBound {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (compiler : NativeCompiler f encIn encOut) (state : compiler.State) :
    compiler.stateEncoding state < compiler.stateBound :=
  letI := compiler.stateFintype
  stateEncoding_lt_stateEncodingBound compiler.stateEncoding state

/-- Forget tidiness while retaining the same named machine and independent bounds. -/
theorem computesInTimeAndSpace {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (compiler : NativeCompiler f encIn encOut) :
    compiler.table.toTM.ComputesFunInTimeAndSpace encIn encOut f compiler.time
      compiler.workspace :=
  fun a => (compiler.computes a).computesInTimeAndSpace

/-- Forget the construction data into the existing plain existential computability predicate.
This direction packages the recorded machine; it does not extract a machine from that predicate. -/
theorem computableInTimeAndSpace {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (compiler : NativeCompiler f encIn encOut) :
    ComputableInTimeAndSpace f encIn encOut compiler.time compiler.workspace :=
  ⟨compiler.tapeCount, compiler.State, @Finite.of_fintype _ compiler.stateFintype,
    compiler.table.toTM,
    compiler.computesInTimeAndSpace⟩

/-- Retype the semantic input of a named compiler when its actual input word is unchanged. The
same machine is retained and no runtime callback is introduced. -/
@[expose] def ofInputEq {α β γ : Type*} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    (compiler : NativeCompiler f encMid encOut) (toInput : α → β)
    (henc : ∀ input, encIn input = encMid (toInput input)) :
    NativeCompiler (fun input => f (toInput input)) encIn encOut :=
  { tapeCount := compiler.tapeCount
    State := compiler.State
    stateFintype := compiler.stateFintype
    table := compiler.table
    stateEncoding := compiler.stateEncoding
    time := fun input => compiler.time (toInput input)
    workspace := fun input => compiler.workspace (toInput input)
    computes := fun input => by
      rw [henc input]
      exact compiler.computes (toInput input) }

/-- Retype the semantic output of a named compiler when the actual emitted word is unchanged. The
same machine and resource maps are retained. -/
@[expose] def ofOutputEq {α β γ : Type*} {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    (compiler : NativeCompiler f encIn encMid)
    (henc : ∀ input, encOut (g input) = encMid (f input)) :
    NativeCompiler g encIn encOut :=
  { tapeCount := compiler.tapeCount
    State := compiler.State
    stateFintype := compiler.stateFintype
    table := compiler.table
    stateEncoding := compiler.stateEncoding
    time := compiler.time
    workspace := compiler.workspace
    computes := fun input => by
      rw [henc input]
      exact compiler.computes input }

/-- The named copy-and-rewind machine. -/
@[expose] def identity {α : Type*} (enc : α ↪ List Bool) :
    NativeCompiler (id : α → α) enc enc := by
  letI : Fintype (Unit ⊕ RewindState) := inferInstance
  exact {
    tapeCount := 0
    State := Unit ⊕ RewindState
    table := MultiTapeMachine.tidyCopy Bool
    stateEncoding := sumStateEncoding unitStateEncoding rewindStateEncoding
    time := fun a => 2 * (enc a).length + 4
    workspace := fun _ => 0
    computes := fun a => MultiTapeMachine.computesTidily_tidyCopy (enc a)
  }

/-- A named constant-output machine with its exact output-length clock and zero workspace. -/
@[expose] def const {α β : Type*} (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (b : β) :
    NativeCompiler (Function.const α b) encIn encOut := by
  let table : MultiTapeMachine 0 Bool (Fin ((encOut b).length + 1)) Empty Id :=
    MultiTapeMachine.ofTr ⟨0, by omega⟩ fun state _ _ =>
      if h : state.val < (encOut b).length then
        { inputTape := 0
          workTapes := Fin.elim0
          output := some (encOut b)[state.val]
          state := some ⟨state.val + 1, by omega⟩ }
      else
        { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
  let cfg (input : List Bool) (n : ℕ) (hn : n ≤ (encOut b).length) :
      Cfg 0 Bool (Fin ((encOut b).length + 1)) input :=
    { state := some ⟨n, by omega⟩
      inputPos := 1
      workTapes := fun i => Fin.elim0 i
      workTapePos := fun i => Fin.elim0 i
      output := (encOut b).take n }
  have step_cfg (input : List Bool) (n : ℕ) (hn : n < (encOut b).length) :
      table.toTM.step (cfg input n hn.le) = cfg input (n + 1) hn := by
    rw [MultiTapeTM.step_of_state rfl]
    simp only [table, MultiTapeMachine.toTM_ofTr, MultiTapeTM.tr_ofTr, dite_eq_left hn]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · simp only [cfg, Action.apply_output, Option.toList_some]
      rw [List.take_add_one, List.getElem?_eq_getElem hn]
      rfl
  have step_cfg_halt (input : List Bool) :
      table.toTM.step (cfg input (encOut b).length le_rfl) =
        wordsCfg input none (fun _ => []) (encOut b) := by
    rw [MultiTapeTM.step_of_state rfl]
    simp only [table, MultiTapeMachine.toTM_ofTr, MultiTapeTM.tr_ofTr,
      dite_eq_right (Nat.not_lt.mpr le_rfl)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · simp [cfg, Action.apply_output]
  have runFrom_cfg (input : List Bool) (n : ℕ) (hn : n ≤ (encOut b).length) :
      table.toTM.runFrom (table.toTM.initCfg input) n = cfg input n hn := by
    induction n with
    | zero => exact Cfg.ext_zero_tapes rfl rfl rfl
    | succ n ih =>
        rw [MultiTapeTM.runFrom_succ, ih (by omega), step_cfg input n (by omega)]
  have computes (input : List Bool) :
      table.toTM.ComputesTidilyInTimeAndSpace input (encOut b)
        ((encOut b).length + 1) 0 := by
    rw [computesTidily_iff_runFrom]
    constructor
    · rw [show wordsCfg input (some table.toTM.q₀) (fun _ => []) [] =
          table.toTM.initCfg input from Cfg.ext_zero_tapes rfl rfl rfl,
        MultiTapeTM.runFrom_succ, runFrom_cfg input (encOut b).length le_rfl,
        step_cfg_halt]
    · simp [MultiTapeNTM.RunPath.space]
  exact {
    tapeCount := 0
    State := Fin ((encOut b).length + 1)
    table := table
    stateEncoding := Fin.valEmbedding
    time := fun _ => (encOut b).length + 1
    workspace := fun _ => 0
    computes := fun a => computes (encIn a)
  }

/-- Direct composition of two named machines. The result contains the choice-free
`MultiTapeMachine.comp` table and retains every constant from its exact time and workspace
theorem. -/
@[expose] def comp {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    (outer : NativeCompiler f encMid encOut) (inner : NativeCompiler g encIn encMid) :
    NativeCompiler (fun a => f (g a)) encIn encOut := by
  let CompilerState :=
    ((inner.State ⊕ RewindWorkState) ⊕
      (MarkWorkState ⊕ outer.State ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState)
  letI := inner.stateFintype
  letI := outer.stateFintype
  letI : Fintype CompilerState := inferInstance
  let table : MultiTapeMachine (max inner.tapeCount outer.tapeCount + 2) Bool CompilerState
      Empty Id := outer.table.comp inner.table true
  exact {
    tapeCount := max inner.tapeCount outer.tapeCount + 2
    State := CompilerState
    table := table
    stateEncoding := sumStateEncoding
      (sumStateEncoding inner.stateEncoding rewindWorkStateEncoding)
      (sumStateEncoding
        (sumStateEncoding markWorkStateEncoding
          (sumStateEncoding outer.stateEncoding markWorkStateEncoding))
        (sumStateEncoding unitStateEncoding rewindWorkStateEncoding))
    time := fun a => inner.time a + outer.time (g a) + 4 * (encMid (g a)).length + 9
    workspace := fun a => inner.workspace a + outer.workspace (g a) +
      5 * (encMid (g a)).length + (6 * max inner.tapeCount outer.tapeCount + 20)
    computes := fun a => MultiTapeMachine.computesTidilyInTimeAndSpace_comp
      (inner.computes a) (outer.computes (g a)) true
  }

/-- Concatenate the raw-word outputs of two named machines on the same input. -/
@[expose] def append {α : Type*} {left right : α → List Bool}
    {encIn : α ↪ List Bool}
    (leftCompiler : NativeCompiler left encIn encBits)
    (rightCompiler : NativeCompiler right encIn encBits) :
    NativeCompiler (fun input => left input ++ right input) encIn encBits := by
  letI := leftCompiler.stateFintype
  letI := rightCompiler.stateFintype
  letI : Fintype (leftCompiler.State ⊕ rightCompiler.State) := inferInstance
  exact {
    tapeCount := max leftCompiler.tapeCount rightCompiler.tapeCount
    State := leftCompiler.State ⊕ rightCompiler.State
    table := leftCompiler.table.append rightCompiler.table
    stateEncoding := sumStateEncoding leftCompiler.stateEncoding rightCompiler.stateEncoding
    time := fun input => leftCompiler.time input + rightCompiler.time input
    workspace := fun input => leftCompiler.workspace input + rightCompiler.workspace input +
      2 * max leftCompiler.tapeCount rightCompiler.tapeCount
    computes := fun input => by
      simpa only [encBits_apply] using MultiTapeMachine.computesTidilyInTimeAndSpace_append
        (leftCompiler.computes input) (rightCompiler.computes input)
  }

/-- The named finite-state transducer that frames an encoded value. -/
@[expose] def encodeFrame {β : Type*} (enc : β ↪ List Bool) :
    NativeCompiler (fun b => frame (enc b)) enc encBits := by
  let FrameState := (Unit × Option Bool × Bool) ⊕ RewindState
  letI : Fintype FrameState := inferInstance
  let frameTable : MultiTapeMachine 0 Bool FrameState Empty Id :=
    Encodings.frameT.toMachine.seq (MultiTapeMachine.rewindInput Bool)
  exact {
    tapeCount := 0
    State := FrameState
    table := frameTable
    stateEncoding := sumStateEncoding
      (transducerMachineStateEncoding unitStateEncoding)
      rewindStateEncoding
    time := fun b => 4 * (enc b).length + 8
    workspace := fun _ => 0
    computes := fun a => by
      rw [MultiTapeMachine.toTM_seq]
      have h := (Encodings.frameT.computesInTimeAndSpace_toTM (enc a))
        |>.computesTidily_seq_explicitRewind
      have hout : encBits (frame (enc a)) =
          Encodings.frameT.run Encodings.frameT.q₀ (enc a) := by
        simpa only [encBits_apply] using (Encodings.frameT_run (enc a)).symm
      rw [hout]
      convert h using 1
      · simp only [Transducer.toTM]
      · omega
  }

universe u v w

/-- Direct standard-pair construction from two named machines on a common input. The left encoded
output is framed by `encodeFrame`, then the right output is appended. -/
@[expose] def pair {α : Type u} {β : Type v} {γ : Type w}
    {f : α → β} {g : α → γ}
    {encIn : α ↪ List Bool} {encLeft : β ↪ List Bool} {encRight : γ ↪ List Bool}
    (left : NativeCompiler f encIn encLeft) (right : NativeCompiler g encIn encRight) :
    NativeCompiler (fun a => (f a, g a)) encIn (encPair encLeft encRight) := by
  let framed := (encodeFrame encLeft).comp left
  letI := framed.stateFintype
  letI := right.stateFintype
  letI : Fintype (framed.State ⊕ right.State) := inferInstance
  exact {
    tapeCount := max framed.tapeCount right.tapeCount
    State := framed.State ⊕ right.State
    table := framed.table.append right.table
    stateEncoding := sumStateEncoding framed.stateEncoding right.stateEncoding
    time := fun a => framed.time a + right.time a
    workspace := fun a => framed.workspace a + right.workspace a +
      2 * max framed.tapeCount right.tapeCount
    computes := fun a => by
      simpa only [encPair_apply, encBits_apply] using
        MultiTapeMachine.computesTidilyInTimeAndSpace_append
          (framed.computes a) (right.computes a)
  }

end NativeCompiler

end Turing.MultiTapeTM.Internal

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Configuration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Option
import Mathlib.Tactic.Linarith

/-!
# Finite configuration operations within quadratic time

The tape and configuration operations used by the step test of views
(`Turing.MultiTapeNTM.viewStepB`) are certified with explicit asymptotic bounds
(`Turing.MultiTapeTM.ComputableInO`). Stack and tape operations, field access, output
summaries and work-tape steps are linear in the encoded configuration; only the clamped move
of the unary input head compares two unary numbers and costs quadratic time. Every operation
uses linear space.

## Main results

* `Turing.MultiTapeTM.ComputableInO.stackTape_head`, `.stackTape_tail`, `.stackTape_cons`,
  `.biTape_mk`, `.biTape_moveLeft`, `.biTape_moveRight`, `.biTape_step`: linear tape operations.
* `Turing.MultiTapeTM.ComputableInO.finiteCfg_mk` and the field projections
  `.finiteCfg_input`, `.finiteCfg_state`, `.finiteCfg_inputPos`, `.finiteCfg_workTapes`,
  `.finiteCfg_output`.
* `Turing.MultiTapeTM.ComputableInO.outputClass`, `.finiteCfg_summarizeOutput`: linear output
  summaries.
* `Turing.MultiTapeTM.ComputableInO.finiteCfg_step`: a fixed native action, within quadratic
  time and linear space.
* `Turing.MultiTapeTM.ComputableInO.finiteCfg_step_summarizeOutput`: a step followed by the
  output summary, within quadratic time and linear space.
* `Turing.MultiTapeTM.ComputableInO.finiteCfg_inputSymbol`, `.finiteCfg_workTapeSymbols`,
  `.finiteCfg_key`: the observations selecting the transitions of a view, in linear time and
  space.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

open Cslib.Turing MultiTapeMachine

section Tape

variable {Symbol α : Type} {input : α ↪ List Bool} {enc : Symbol ↪ List Bool}
  {T₁ S₁ T₂ S₂ T₃ S₃ : α → ℕ}

private theorem stackTape_toList (enc : Symbol ↪ List Bool) :
    ComputableInO StackTape.toList (encStackTape enc) (encList (encOption enc))
      (fun tape => (encStackTape enc tape).length)
      (fun tape => (encStackTape enc tape).length) :=
  of_eq fun _ => rfl

/-- The head of a stack, with a blank default, in linear time and space. -/
theorem stackTape_head (enc : Symbol ↪ List Bool) :
    ComputableInO StackTape.head (encStackTape enc) (encOption enc)
      (fun tape => (encStackTape enc tape).length)
      (fun tape => (encStackTape enc tape).length) :=
  ((headD' (enc := encOption enc) none).comp_linear (stackTape_toList enc)).of_enc_eq
    fun tape => by cases tape with | mk values h => cases values <;> rfl

/-- Removing the head of a stack, in linear time and space. -/
theorem stackTape_tail (enc : Symbol ↪ List Bool) :
    ComputableInO StackTape.tail (encStackTape enc) (encStackTape enc)
      (fun tape => (encStackTape enc tape).length)
      (fun tape => (encStackTape enc tape).length) :=
  ((tail' (enc := encOption enc)).comp_linear (stackTape_toList enc)).of_enc_eq fun tape => by
    simp only [Function.comp_def, encStackTape_apply, StackTape.tail_toList]

private theorem stackTape_cons_pair (enc : Symbol ↪ List Bool) :
    ComputableInO (fun p : Option Symbol × StackTape Symbol => StackTape.cons p.1 p.2)
      (encPair (encOption enc) (encStackTape enc)) (encStackTape enc)
      (fun p => (encPair (encOption enc) (encStackTape enc) p).length)
      (fun p => (encPair (encOption enc) (encStackTape enc) p).length) := by
  have hsymbol := fst (encOption enc) (encStackTape enc)
  have hcells := (stackTape_toList enc).comp_linear (snd (encOption enc) (encStackTape enc))
  have hcond := or' (optionIsSome hsymbol)
    (not' ((ComputableInDegree.listIsEmpty (encOption enc)).inO_one.comp_linear hcells))
  have hlist := hcond.ite (cons'.comp_linear (hsymbol.prod hcells)) (const [])
  refine (hlist.of_enc_eq fun p => ?_).mono 4 (fun p => ?_) fun p => ?_
  · rw [encStackTape_apply, StackTape.cons_toList]
    rfl
  all_goals split_ifs <;> omega

/-- Prepend a computed cell to a computed stack, retaining its omission of trailing blanks. -/
theorem stackTape_cons {symbol : α → Option Symbol} {tape : α → StackTape Symbol}
    (hsymbol : ComputableInO symbol input (encOption enc) T₁ S₁)
    (htape : ComputableInO tape input (encStackTape enc) T₂ S₂) :
    ComputableInO (fun a => StackTape.cons (symbol a) (tape a)) input (encStackTape enc)
      (fun a => T₁ a + T₂ a) (fun a => S₁ a + S₂ a) :=
  (stackTape_cons_pair enc).comp_linear (hsymbol.prod htape)

private theorem biTape_parts (enc : Symbol ↪ List Bool) :
    ComputableInO (fun tape : BiTape Symbol => (tape.head, tape.left, tape.right))
      (encBiTape enc) (encPair (encOption enc) (encPair (encStackTape enc) (encStackTape enc)))
      (fun tape => (encBiTape enc tape).length) (fun tape => (encBiTape enc tape).length) :=
  of_eq fun _ => rfl

/-- Assemble a tape from its computed head and two sides. -/
theorem biTape_mk {head : α → Option Symbol} {left right : α → StackTape Symbol}
    (hhead : ComputableInO head input (encOption enc) T₁ S₁)
    (hleft : ComputableInO left input (encStackTape enc) T₂ S₂)
    (hright : ComputableInO right input (encStackTape enc) T₃ S₃) :
    ComputableInO (fun a => BiTape.mk (head a) (left a) (right a)) input (encBiTape enc)
      (fun a => T₁ a + (T₂ a + T₃ a)) (fun a => S₁ a + (S₂ a + S₃ a)) :=
  (hhead.prod (hleft.prod hright)).of_enc_eq fun _ => rfl

/-- Read the current cell of a tape. -/
theorem biTape_head (enc : Symbol ↪ List Bool) :
    ComputableInO BiTape.head (encBiTape enc) (encOption enc)
      (fun tape => (encBiTape enc tape).length) (fun tape => (encBiTape enc tape).length) :=
  (biTape_parts enc).fst'

/-- Extract the stored left side of a tape. -/
theorem biTape_left (enc : Symbol ↪ List Bool) :
    ComputableInO BiTape.left (encBiTape enc) (encStackTape enc)
      (fun tape => (encBiTape enc tape).length) (fun tape => (encBiTape enc tape).length) :=
  (biTape_parts enc).snd'.fst'

/-- Extract the stored right side of a tape. -/
theorem biTape_right (enc : Symbol ↪ List Bool) :
    ComputableInO BiTape.right (encBiTape enc) (encStackTape enc)
      (fun tape => (encBiTape enc tape).length) (fun tape => (encBiTape enc tape).length) :=
  (biTape_parts enc).snd'.snd'

/-- Move the head left by the stack operations, in linear time and space. -/
theorem biTape_moveLeft (enc : Symbol ↪ List Bool) :
    ComputableInO BiTape.moveLeft (encBiTape enc) (encBiTape enc)
      (fun tape => (encBiTape enc tape).length) (fun tape => (encBiTape enc tape).length) :=
  (biTape_mk ((stackTape_head enc).comp_linear (biTape_left enc))
    ((stackTape_tail enc).comp_linear (biTape_left enc))
    (stackTape_cons (biTape_head enc) (biTape_right enc))).mono 4
    (fun _ => by omega) fun _ => by omega

/-- Move the head right by the stack operations, in linear time and space. -/
theorem biTape_moveRight (enc : Symbol ↪ List Bool) :
    ComputableInO BiTape.moveRight (encBiTape enc) (encBiTape enc)
      (fun tape => (encBiTape enc tape).length) (fun tape => (encBiTape enc tape).length) :=
  (biTape_mk ((stackTape_head enc).comp_linear (biTape_right enc))
    (stackTape_cons (biTape_head enc) (biTape_left enc))
    ((stackTape_tail enc).comp_linear (biTape_right enc))).mono 4
    (fun _ => by omega) fun _ => by omega

/-- Execute a fixed native tape action, in linear time and space. -/
theorem biTape_step (enc : Symbol ↪ List Bool) (action : Option (Option Symbol) × SignType) :
    ComputableInO (fun tape : BiTape Symbol => tape.step action) (encBiTape enc) (encBiTape enc)
      (fun tape => (encBiTape enc tape).length) (fun tape => (encBiTape enc tape).length) := by
  rcases action with ⟨write, move⟩
  have hwritten : ComputableInO (fun tape : BiTape Symbol => write.elim tape tape.write)
      (encBiTape enc) (encBiTape enc)
      (fun tape => (encBiTape enc tape).length) (fun tape => (encBiTape enc tape).length) := by
    cases write with
    | none => exact id'
    | some symbol =>
      exact (biTape_mk (const symbol) (biTape_left enc) (biTape_right enc)).mono 3
        (fun _ => by omega) fun _ => by omega
  cases move with
  | zero => exact hwritten
  | neg => exact (biTape_moveLeft enc).comp_linear hwritten
  | pos => exact (biTape_moveRight enc).comp_linear hwritten

end Tape

/-- The output summary on raw words, in linear time and space. -/
theorem outputClass :
    ComputableInO MultiTapeNTM.outputClass encBits encBits
      (fun word => (encBits word).length) (fun word => (encBits word).length) := by
  have heq (word : List Bool) : MultiTapeNTM.outputClass word = if word.isEmpty then [] else
      if word.tail.isEmpty && word.headD false then [true] else [false] := by
    rcases word with _ | ⟨_ | _, _ | ⟨_, _⟩⟩ <;> simp [MultiTapeNTM.outputClass]
  have hempty := (ComputableInDegree.isEmpty (enc₁ := encBool) (enc := encBits)).inO_one
  have htail := (ComputableInDegree.tail (enc₁ := encBool) (enc := encBits)).inO_one
  have hhead := (ComputableInDegree.headD (enc₁ := encBool) (enc := encBits) false).inO_one
  refine ((hempty.ite (const []) ((and' (hempty.comp_linear htail) hhead).ite (const [true])
    (const [false]))).of_enc_eq fun word => congrArg encBits (heq word)).mono 4
    (fun word => ?_) fun word => ?_ <;> split_ifs <;> omega

section Configuration

variable {k : ℕ} {State α : Type} [Finite State] {input : α ↪ List Bool}

/-- Assemble a configuration from its computed components, adding their bounds. -/
theorem finiteCfg_mk {word : α → List Bool} {state : α → Option State}
    {position : ∀ a, Fin ((word a).length + 2)} {work : α → Fin k → BiTape Bool}
    {output : α → List Bool} {T₁ S₁ T₂ S₂ T₃ S₃ T₄ S₄ T₅ S₅ : α → ℕ}
    (hword : ComputableInO word input encBits T₁ S₁)
    (hstate : ComputableInO state input (encFinite (Option State)) T₂ S₂)
    (hposition : ComputableInO (fun a => (position a).val) input encUnary T₃ S₃)
    (hwork : ComputableInO work input (encPi (encBiTape encBool)) T₄ S₄)
    (houtput : ComputableInO output input encBits T₅ S₅) :
    ComputableInO (fun a =>
      (⟨word a, state a, position a, work a, output a⟩ : FiniteCfg k Bool State))
      input encFiniteCfg (fun a => T₁ a + (T₂ a + (T₃ a + (T₄ a + T₅ a))))
      (fun a => S₁ a + (S₂ a + (S₃ a + (S₄ a + S₅ a)))) :=
  (hword.prod (hstate.prod (hposition.prod (hwork.prod houtput)))).of_enc_eq fun _ => rfl

private theorem finiteCfg_parts : ComputableInO
    (fun cfg : FiniteCfg k Bool State =>
      (cfg.input, cfg.state, cfg.inputPos.val, cfg.workTapes, cfg.output)) encFiniteCfg
    (encPair encBits (encPair (encFinite (Option State))
      (encPair encUnary (encPair (encPi (encBiTape encBool)) encBits))))
    (fun cfg => (encFiniteCfg cfg).length) (fun cfg => (encFiniteCfg cfg).length) :=
  of_eq fun _ => rfl

/-- Read the stored input word of a configuration. -/
theorem finiteCfg_input : ComputableInO (FiniteCfg.input (k := k) (State := State))
    encFiniteCfg encBits (fun cfg => (encFiniteCfg cfg).length)
    (fun cfg => (encFiniteCfg cfg).length) :=
  finiteCfg_parts.fst'

/-- Read the finite control of a configuration. -/
theorem finiteCfg_state : ComputableInO (FiniteCfg.state (k := k) (State := State))
    encFiniteCfg (encFinite (Option State)) (fun cfg => (encFiniteCfg cfg).length)
    (fun cfg => (encFiniteCfg cfg).length) :=
  finiteCfg_parts.snd'.fst'

/-- Read the unary input-head position of a configuration. -/
theorem finiteCfg_inputPos : ComputableInO
    (fun cfg : FiniteCfg k Bool State => cfg.inputPos.val) encFiniteCfg encUnary
    (fun cfg => (encFiniteCfg cfg).length) (fun cfg => (encFiniteCfg cfg).length) :=
  finiteCfg_parts.snd'.snd'.fst'

/-- Read the family of work tapes of a configuration. -/
theorem finiteCfg_workTapes : ComputableInO (FiniteCfg.workTapes (k := k) (State := State))
    encFiniteCfg (encPi (encBiTape encBool)) (fun cfg => (encFiniteCfg cfg).length)
    (fun cfg => (encFiniteCfg cfg).length) :=
  finiteCfg_parts.snd'.snd'.snd'.fst'

/-- Read the accumulated output of a configuration. -/
theorem finiteCfg_output : ComputableInO (FiniteCfg.output (k := k) (State := State))
    encFiniteCfg encBits (fun cfg => (encFiniteCfg cfg).length)
    (fun cfg => (encFiniteCfg cfg).length) :=
  finiteCfg_parts.snd'.snd'.snd'.snd'

private theorem length_fields_le (cfg : FiniteCfg k Bool State) :
    cfg.input.length + cfg.inputPos.val + cfg.output.length ≤ (encFiniteCfg cfg).length := by
  simp only [encFiniteCfg_apply, length_encPair, encBits_apply, encUnary_apply,
    List.length_replicate]
  omega

/-- The clamped native move of the unary input head, within quadratic time and linear space:
moving right compares the position with the input length. -/
theorem finiteCfg_moveInputPos (move : SignType) : ComputableInO
    (fun cfg : FiniteCfg k Bool State => (Turing.moveInputPos cfg.inputPos move).val)
    encFiniteCfg encUnary (fun cfg => ((encFiniteCfg cfg).length + 1) ^ 2)
    (fun cfg => (encFiniteCfg cfg).length) := by
  cases move with
  | neg =>
    refine ((unaryPred'.comp_linear finiteCfg_inputPos).of_enc_eq fun cfg => ?_).mono 1
      (fun cfg => by nlinarith) fun cfg => by omega
    apply congrArg encUnary
    have h := val_moveInputPos_eq cfg.inputPos .neg
    have hp := cfg.inputPos.isLt
    simp only [SignType.cast, Function.comp_def] at h ⊢
    lia
  | zero =>
    refine (finiteCfg_inputPos.of_enc_eq fun cfg => ?_).mono 1
      (fun cfg => by nlinarith) fun cfg => by omega
    apply congrArg encUnary
    have h := val_moveInputPos_eq cfg.inputPos .zero
    simp only [SignType.cast] at h ⊢
    lia
  | pos =>
    have hle := unaryLe.comp ((finiteCfg_inputPos (k := k) (State := State)).prod
      (bitsLengthUnary' finiteCfg_input))
    refine ((hle.ite (unarySucc'.comp_linear finiteCfg_inputPos) finiteCfg_inputPos).of_enc_eq
      fun cfg => ?_).mono 9 (fun cfg => ?_) fun cfg => ?_
    · apply congrArg encUnary
      have h := val_moveInputPos_eq cfg.inputPos .pos
      have hp := cfg.inputPos.isLt
      simp only [SignType.cast, Function.comp_def] at h ⊢
      split_ifs with hc <;> simp only [decide_eq_true_eq] at hc <;> omega
    all_goals
      have hfields := length_fields_le cfg
      have hpair : (encPair encUnary encUnary (cfg.inputPos.val, cfg.input.length)).length ≤
          3 * (encFiniteCfg cfg).length + 1 := by
        simp only [length_encPair, encUnary_apply, List.length_replicate]
        omega
      simp only [Function.comp_def] at *
      split_ifs <;> nlinarith

/-- Execute fixed native actions on all work tapes, in linear time and space. -/
theorem finiteCfg_stepWorkTapes (action : Fin k → Option (Option Bool) × SignType) :
    ComputableInO
      (fun cfg : FiniteCfg k Bool State => fun tape => (cfg.workTapes tape).step (action tape))
      encFiniteCfg (encPi (encBiTape encBool)) (fun cfg => (encFiniteCfg cfg).length)
      (fun cfg => (encFiniteCfg cfg).length) :=
  (pi fun tape => (biTape_step encBool (action tape)).comp_linear
    ((pi_apply _ tape).comp_linear finiteCfg_workTapes)).mono (k + 1)
    (fun _ => by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
                 nlinarith)
    fun _ => by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
                nlinarith

/-- Execute a fixed native action on a configuration, within quadratic time and linear space. -/
theorem finiteCfg_step (action : Action k Bool State) :
    ComputableInO (fun cfg : FiniteCfg k Bool State => cfg.step action) encFiniteCfg
      encFiniteCfg (fun cfg => ((encFiniteCfg cfg).length + 1) ^ 2)
      (fun cfg => (encFiniteCfg cfg).length) :=
  (finiteCfg_mk finiteCfg_input (const _) (finiteCfg_moveInputPos action.inputTape)
    (finiteCfg_stepWorkTapes action.workTapes) (bitsAppend' finiteCfg_output (const _))).mono 6
    (fun _ => by nlinarith) fun _ => by omega

/-- Summarizing the output of a configuration, in linear time and space. -/
theorem finiteCfg_summarizeOutput :
    ComputableInO (FiniteCfg.summarizeOutput (k := k) (State := State)) encFiniteCfg
      encFiniteCfg (fun cfg => (encFiniteCfg cfg).length)
      (fun cfg => (encFiniteCfg cfg).length) :=
  (finiteCfg_mk finiteCfg_input finiteCfg_state finiteCfg_inputPos finiteCfg_workTapes
    (outputClass.comp_linear finiteCfg_output)).mono 5 (fun _ => by omega) fun _ => by omega

/-- **A step of views**: a fixed native action followed by the output summary, within quadratic
time and linear space (hence with a linear encoded output). -/
theorem finiteCfg_step_summarizeOutput (action : Action k Bool State) :
    ComputableInO (fun cfg : FiniteCfg k Bool State => (cfg.step action).summarizeOutput)
      encFiniteCfg encFiniteCfg (fun cfg => ((encFiniteCfg cfg).length + 1) ^ 2)
      (fun cfg => (encFiniteCfg cfg).length) :=
  finiteCfg_summarizeOutput.comp_linear (finiteCfg_step action)

/-- A step of views has a linearly bounded encoding. -/
theorem length_encFiniteCfg_step_summarizeOutput_le (action : Action k Bool State) :
    ∃ c, ∀ cfg : FiniteCfg k Bool State,
      (encFiniteCfg ((cfg.step action).summarizeOutput)).length ≤
        c * ((encFiniteCfg cfg).length + 1) :=
  (finiteCfg_step_summarizeOutput action).length_le

omit [Finite State] in
private theorem inputSymbol_eq (cfg : FiniteCfg k Bool State) :
    cfg.inputSymbol = if decide (cfg.inputPos.val = 0) = true then none
      else (cfg.input.drop (cfg.inputPos.val - 1)).head? := by
  rw [FiniteCfg.inputSymbol_eq_getD]
  rcases cfg with ⟨word, state, ⟨_ | j, hj⟩, work, output⟩
  · simp
  · simp only [Nat.add_one_ne_zero, decide_false, Bool.false_eq_true, ite_false,
      Nat.add_sub_cancel, List.head?_drop, List.getElem?_cons_succ, List.getElem?_map]
    cases word[j]? <;> rfl

/-- Observe the read-only input of a configuration, including both blank boundary cells, in
linear time and space. -/
theorem finiteCfg_inputSymbol : ComputableInO (FiniteCfg.inputSymbol (k := k) (State := State))
    encFiniteCfg (encFinEnum (Option Bool)) (fun cfg => (encFiniteCfg cfg).length)
    (fun cfg => (encFiniteCfg cfg).length) := by
  have hpos := finiteCfg_inputPos (k := k) (State := State)
  have hcells := (ComputableInDegree.dropUnary encBool).inO_one.comp_linear
    ((ComputableInDegree.bitsToList.inO_one.comp_linear finiteCfg_input).prod
      (unaryPred'.comp_linear hpos))
  have hsymbol := (ComputableInDegree.unary_isZero.inO_one.comp_linear hpos).ite (const none)
    ((ComputableInDegree.head?_one (enc := encBool)).inO_one.comp_linear hcells)
  refine (((ComputableInDegree.of_finite (encIn := encOption encBool)
    (encMid := encFinEnum (Option Bool)) id).inO_one.comp_linear hsymbol).of_enc_eq
    fun cfg => congrArg _ ?_).mono 3 (fun cfg => ?_) fun cfg => ?_
  · rw [inputSymbol_eq]
    rfl
  all_goals split_ifs <;> omega

/-- Observe all work heads of a configuration as one finite value, in linear time and space. -/
theorem finiteCfg_workTapeSymbols : ComputableInO
    (FiniteCfg.workTapeSymbols (k := k) (State := State)) encFiniteCfg
    (encFinEnum (Fin k → Option Bool)) (fun cfg => (encFiniteCfg cfg).length)
    (fun cfg => (encFiniteCfg cfg).length) :=
  ((ComputableInDegree.of_finite id).inO_one.comp_linear
    (pi fun tape => (biTape_head encBool).comp_linear
      ((pi_apply _ tape).comp_linear finiteCfg_workTapes))).mono (k + 1)
    (fun _ => by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
                 nlinarith)
    fun _ => by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
                nlinarith

/-- **The finite key of a view**: its control, input symbol and work symbols, which select its
transitions, in linear time and space. -/
theorem finiteCfg_key : ComputableInO
    (fun cfg : FiniteCfg k Bool State => (cfg.state, cfg.inputSymbol, cfg.workTapeSymbols))
    encFiniteCfg (encPair (encFinite _) (encPair (encFinEnum _) (encFinEnum _)))
    (fun cfg => (encFiniteCfg cfg).length) (fun cfg => (encFiniteCfg cfg).length) :=
  (finiteCfg_state.prod (finiteCfg_inputSymbol.prod finiteCfg_workTapeSymbols)).mono 3
    (fun _ => by omega) fun _ => by omega

end Configuration

end Turing.MultiTapeTM.ComputableInO

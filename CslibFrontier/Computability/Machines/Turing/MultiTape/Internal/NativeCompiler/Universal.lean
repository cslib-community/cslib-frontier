/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Conditional
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Equality
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Complexity

/-!
# Named native deterministic-universal primitives

This module retains the concrete machines used by encoded deterministic and probabilistic
universal steps. Each construction is assembled from named native projections, streaming codecs,
arithmetic machines and conditionals; no semantic function is installed as an opaque machine.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.inputSymbol`: retained binary-position input lookup.
* `Turing.MultiTapeTM.Internal.NativeCompiler.moveInput`: retained boundary-aware input-head move.
* `Turing.MultiTapeTM.Internal.NativeCompiler.actInputMove`, `.actWorkActions`, `.actOutput`,
  `.actState`: retained ordinary-action projections.
* `Turing.MultiTapeTM.Internal.NativeCompiler.tapeRead`, `.tapeApply`, `.reads`, `.applyTapes`:
  retained work-tape reads and updates.
* `Turing.MultiTapeTM.Internal.NativeCompiler.intUnaryPayload`, `.intUnaryNonnegativeTest`:
  retained signed-unary tag and payload access.
* `Turing.MultiTapeTM.Internal.NativeCompiler.intSucc`, `.intPred`, `.intMove`: retained
  signed-unary successor, predecessor and sign-directed movement.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM.Universal

private abbrev MoveInput := ℕ × (Option ℕ × SignType)
private abbrev eMoveInput : MoveInput ↪ List Bool := encPair encNat (encPair eSym encSign)
private abbrev TapeTail := List (Option ℕ) × List (Option ℕ)
private abbrev eTapeTail : TapeTail ↪ List Bool := encPair (encList eSym) (encList eSym)
private abbrev ActTail₃ := List TapeAct × (Option ℕ × Option ℕ)
private abbrev ActTail₂ := Option ℕ × Option ℕ
private abbrev eActTail₃ : ActTail₃ ↪ List Bool :=
  encPair (encList eTA) (encPair eSym eSym)
private abbrev eActTail₂ : ActTail₂ ↪ List Bool := encPair eSym eSym

/-- Retained projection of the ordinary input-head movement. -/
noncomputable def actInputMove : NativeCompiler Act.inputTape eAct encSign :=
  (first encSign eActTail₃).ofInputEq
    (fun action : Act => (action.inputTape, action.workTapes, action.output, action.state))
    fun _ => rfl

/-- Retained projection of the ordinary-action tail after input movement. -/
noncomputable def actTail₃ :
    NativeCompiler (fun action : Act => (action.workTapes, action.output, action.state))
      eAct eActTail₃ :=
  (second encSign eActTail₃).ofInputEq
    (fun action : Act => (action.inputTape, action.workTapes, action.output, action.state))
    fun _ => rfl

/-- Retained projection of work-tape actions. -/
noncomputable def actWorkActions :
    NativeCompiler Act.workTapes eAct (encList eTA) :=
  (first (encList eTA) eActTail₂).comp actTail₃

/-- Retained ordinary-action output and successor tail. -/
noncomputable def actTail₂ :
    NativeCompiler (fun action : Act => (action.output, action.state)) eAct eActTail₂ :=
  (second (encList eTA) eActTail₂).comp actTail₃

/-- Retained projection of the optional ordinary output symbol. -/
noncomputable def actOutput : NativeCompiler Act.output eAct eSym :=
  (first eSym eSym).comp actTail₂

/-- Retained projection of the optional ordinary successor tag. -/
noncomputable def actState : NativeCompiler Act.state eAct eSym :=
  (second eSym eSym).comp actTail₂

/-- Payload stored after the signed-unary tag bit. The negative branch is used only when clients
explicitly accept that constructor. -/
@[expose] def intUnaryPayload : ℤ → ℕ
  | .ofNat value => value
  | .negSucc value => value

/-- Retained removal of the signed-unary tag bit. -/
@[expose] noncomputable def intUnaryPayloadCompiler :
    NativeCompiler intUnaryPayload encIntUnary encUnary :=
  (tailDecoder.ofInputEq (fun value => encIntUnary value) fun _ => rfl).ofOutputEq
    fun value => by cases value <;> rfl

/-- Retained nonnegative signed-unary constructor test. -/
@[expose] noncomputable def intUnaryNonnegativeTest :
    NativeCompiler (fun value : ℤ => decide (0 ≤ value)) encIntUnary encTest := by
  let sign := boolDecoder.ofInputEq (fun value => encIntUnary value) fun _ => rfl
  let negative := boolToTest.comp sign
  let yes := const encIntUnary encTest true
  let no := const encIntUnary encTest false
  exact (ite negative no yes).ofOutputEq fun value => by cases value <;> rfl

/-- Retained signed-unary successor through the existing concrete transducer. -/
@[expose] noncomputable def intSucc :
    NativeCompiler (fun value : ℤ => value + 1) encIntUnary encIntUnary :=
  ofTransducer EncIntUnary.succT Fin.valEmbedding fun value => by
    have copy := Transducer.run_eq_self EncIntUnary.succT 2
      (fun bit => by cases bit <;> rfl) rfl
    rcases value with n | _ | n
    · simp [copy]
    · rfl
    · change encIntUnary (Int.negSucc n) = _
      simp [copy, List.replicate_succ]

/-- Retained signed-unary predecessor through the existing concrete transducer. -/
@[expose] noncomputable def intPred :
    NativeCompiler (fun value : ℤ => value - 1) encIntUnary encIntUnary :=
  ofTransducer EncIntUnary.predT Fin.valEmbedding fun value => by
    have copy := Transducer.run_eq_self EncIntUnary.predT 2
      (fun bit => by cases bit <;> rfl) rfl
    rcases value with (_ | n) | n
    · rfl
    · simp [copy]
    · simp [copy, List.replicate_succ]

/-- Retained sign-directed integer movement. -/
@[expose] noncomputable def intMove :
    NativeCompiler (fun input : ℤ × SignType => input.1 + input.2)
      (encPair encIntUnary encSign) encIntUnary := by
  let value := first encIntUnary encSign
  let movement := second encIntUnary encSign
  let signIs (sign : SignType) := (wordEqTest encSign).comp
    (movement.pair (const (encPair encIntUnary encSign) encSign sign))
  let stay := value
  let positive := intSucc.comp value
  let negative := intPred.comp value
  refine (ite (signIs .zero) stay (ite (signIs .neg) negative positive)).ofOutputEq ?_
  rintro ⟨value, movement⟩
  cases movement <;> rfl

/-- Retained projection of a zipper's two cell lists. -/
noncomputable def tapeTail :
    NativeCompiler (fun tape : Tape => (tape.left, tape.right)) eTape eTapeTail :=
  (second encIntUnary eTapeTail).ofInputEq
    (fun tape : Tape => (tape.head, tape.left, tape.right)) fun _ => rfl

/-- Retained projection of a zipper's signed head position. -/
noncomputable def tapeHead : NativeCompiler Tape.head eTape encIntUnary :=
  (first encIntUnary eTapeTail).ofInputEq
    (fun tape : Tape => (tape.head, tape.left, tape.right)) fun _ => rfl

/-- Retained projection of cells left of the work-tape head. -/
noncomputable def tapeLeft : NativeCompiler Tape.left eTape (encList eSym) :=
  (first (encList eSym) (encList eSym)).comp tapeTail

/-- Retained projection of the cells at and right of the work-tape head. -/
noncomputable def tapeRight :
    NativeCompiler Tape.right eTape (encList eSym) :=
  (second (encList eSym) (encList eSym)).comp tapeTail

/-- Retained work-tape head read, returning blank on an empty right half. -/
@[expose] noncomputable def tapeRead : NativeCompiler Tape.read eTape eSym :=
  ((listHeadD none eSym).comp tapeRight).ofOutputEq fun tape => by
    rfl

/-- Retained work-tape write, rebuilding the zipper from named field/list machines. -/
@[expose] noncomputable def tapeWrite :
    NativeCompiler (fun input : Tape × Option ℕ => input.1.write input.2)
      (encPair eTape eSym) eTape := by
  let tape := first eTape eSym
  let symbol := second eTape eSym
  let head := tapeHead.comp tape
  let left := tapeLeft.comp tape
  let right := tapeRight.comp tape
  let rightTail := (listTailCompiler eSym).comp right
  let newRight := (listConsCompiler eSym).comp (symbol.pair rightTail)
  exact head.pair (left.pair newRight) |>.ofOutputEq fun _ => rfl

/-- Retained positive work-tape move. -/
@[expose] noncomputable def tapeMovePos :
    NativeCompiler (fun tape : Tape => tape.move .pos) eTape eTape := by
  let head := intSucc.comp tapeHead
  let left := (listConsCompiler eSym).comp (tapeRead.pair tapeLeft)
  let right := (listTailCompiler eSym).comp tapeRight
  exact head.pair (left.pair right) |>.ofOutputEq fun _ => rfl

/-- Retained negative work-tape move. -/
@[expose] noncomputable def tapeMoveNeg :
    NativeCompiler (fun tape : Tape => tape.move .neg) eTape eTape := by
  let head := intPred.comp tapeHead
  let left := (listTailCompiler eSym).comp tapeLeft
  let leftHead := (listHeadD none eSym).comp tapeLeft
  let right := (listConsCompiler eSym).comp (leftHead.pair tapeRight)
  exact head.pair (left.pair right) |>.ofOutputEq fun _ => rfl

/-- Retained signed work-tape movement. -/
@[expose] noncomputable def tapeMove :
    NativeCompiler (fun input : Tape × SignType => input.1.move input.2)
      (encPair eTape encSign) eTape := by
  let tape := first eTape encSign
  let movement := second eTape encSign
  let signIs (sign : SignType) := (wordEqTest encSign).comp
    (movement.pair (const (encPair eTape encSign) encSign sign))
  let stay := tape
  let positive := tapeMovePos.comp tape
  let negative := tapeMoveNeg.comp tape
  refine (ite (signIs .zero) stay (ite (signIs .neg) negative positive)).ofOutputEq ?_
  rintro ⟨tape, movement⟩
  cases movement <;> rfl

/-- Retained optional write followed by retained signed movement. -/
@[expose] noncomputable def tapeApply :
    NativeCompiler (fun input : Tape × TapeAct => input.1.apply input.2)
      (encPair eTape eTA) eTape := by
  let encInput := encPair eTape eTA
  let tape := first eTape eTA
  let action := second eTape eTA
  let write := (first (encOption eSym) encSign).comp action
  let movement := (second (encOption eSym) encSign).comp action
  let hasWrite := (optionIsSomeTest eSym).comp write
  let symbol := (optionGetD none eSym).comp write
  let written := ite hasWrite (tapeWrite.comp (tape.pair symbol)) tape
  refine (tapeMove.comp (written.pair movement)).ofOutputEq ?_
  rintro ⟨tape, ⟨write, movement⟩⟩
  cases write <;> rfl

/-- Retained left-length application of work-tape actions. Missing actions use `(none, zero)` and
extra actions are ignored exactly as in the source interpreter. -/
@[expose] noncomputable def applyTapes :
    NativeCompiler (fun input : List Tape × List TapeAct =>
      Turing.MultiTapeTM.Universal.applyTapes input.1 input.2)
      (encPair (encList eTape) (encList eTA)) (encList eTape) := by
  let zipped := listZipWithLeftCompiler (none, .zero) eTape eTA eTape tapeApply
  refine zipped.ofOutputEq ?_
  intro input
  apply congrArg (encList eTape)
  induction input.1 generalizing input.2 with
  | nil => rfl
  | cons tape tapes ih =>
      cases input.2 <;> simp [listZipWithLeft, Turing.MultiTapeTM.Universal.applyTapes, ih]

/-- Retained work-head reads, executing the named tape-read callback once per zipper. -/
@[expose] noncomputable def reads :
    NativeCompiler (List.map Tape.read) (encList eTape) (encList eSym) :=
  listMapCompiler eTape eSym tapeRead

/-- Retained input-symbol lookup. Position zero is the left blank; positive positions use a
binary predecessor followed by the charged binary-indexed list scan. -/
@[expose] noncomputable def inputSymbol :
    NativeCompiler (fun input : List ℕ × ℕ =>
      Turing.MultiTapeTM.Universal.inputSymbol input.1 input.2)
      (encPair (encList encUnary) encNat) eSym := by
  let encInput := encPair (encList encUnary) encNat
  let word := first (encList encUnary) encNat
  let position := second (encList encUnary) encNat
  let atLeftBoundary := natIsZeroTest.comp position
  let blank := const encInput eSym none
  let index := natPred.comp position
  let lookup := (listGet?NatCompiler encUnary).comp (word.pair index)
  refine (ite atLeftBoundary blank lookup).ofOutputEq ?_
  rintro ⟨word, position⟩
  cases position <;> simp [Turing.MultiTapeTM.Universal.inputSymbol, List.head?_drop]

/-- Retained boundary-aware input-head movement. The positive branch tests binary zero and the
standard option tag explicitly before selecting the concrete successor or identity machines. -/
@[expose] noncomputable def moveInput :
    NativeCompiler (fun input : MoveInput =>
      Turing.MultiTapeTM.Universal.moveInput input.1 input.2.1 input.2.2)
      eMoveInput encNat := by
  let position := first encNat (encPair eSym encSign)
  let tail := second encNat (encPair eSym encSign)
  let symbol := (first eSym encSign).comp tail
  let movement := (second eSym encSign).comp tail
  let signIs (sign : SignType) := (wordEqTest encSign).comp
    (movement.pair (const eMoveInput encSign sign))
  let stay := position
  let predecessor := natPred.comp position
  let successor := natSucc.comp position
  let atLeftBoundary := natIsZeroTest.comp position
  let readsSymbol := (optionIsSomeTest encUnary).comp symbol
  let positive := ite atLeftBoundary successor (ite readsSymbol successor stay)
  let assembled := ite (signIs .zero) stay (ite (signIs .neg) predecessor positive)
  refine assembled.ofOutputEq ?_
  rintro ⟨position, symbol, movement⟩
  cases movement <;> cases position <;> cases symbol <;>
    simp [assembled, positive, signIs, Turing.MultiTapeTM.Universal.moveInput]

end Turing.MultiTapeTM.Internal.NativeCompiler

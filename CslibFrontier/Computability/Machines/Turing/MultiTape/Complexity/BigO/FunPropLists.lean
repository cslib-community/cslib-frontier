/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeUnaryPrimitives

/-!
# `fun_prop` rules for list, option, number and test operations

These rules assemble `Turing.MultiTapeTM.ComputableInO` certificates with explicit time and
charged-space bounds. `fun_prop` composes the primitives through
`Turing.MultiTapeTM.ComputableInO.comp'`; `Turing.MultiTapeTM.ComputableInO.mono` then compares
the assembled bounds with the client's target bounds.

The list, option, bit-word and unary-number primitives are linear in their encoded arguments.
Captured framing, option-to-list and unary-length rules compose linearly via
`Turing.MultiTapeTM.ComputableInO.comp_linear`, preserving the inner computation's bounds without
adding an output-length term. The registered binary `natSucc` and `natPred` certificates instead
have quadratic time and linear charged space. General equality `eq'` adds its explicit
product-of-lengths time charge and encoded-pair space charge; clients enable it locally. Tests
against a fixed value of a finite type and binary zero retain the tested computation's bounds,
whereas `isEmpty'` adds the computed list's encoded length to both time and space. A test takes
that computation as a premise, since its Boolean result does not determine the tested value's
encoding.

## Main results

* `Turing.MultiTapeTM.ComputableInO.take'`, `.drop'`: prefixes and suffixes of a list, with a unary
  count.
* `Turing.MultiTapeTM.ComputableInO.listAppend'`, `.frame'`, `.unframe'`, `.dropFrame'`,
  `.bitsAppend'`: list concatenation, framing and bit-string concatenation preserving producer
  bounds.
* `Turing.MultiTapeTM.ComputableInO.optionToList`, `.optionToList'`: option-to-list conversion
  without assuming an inhabited payload type.
* `Turing.MultiTapeTM.ComputableInO.bitsLengthUnary'`: unary length of a computed bit string.
* `Turing.MultiTapeTM.ComputableInO.not'`, `.and'`, `.or'`: Boolean connectives.
* `Turing.MultiTapeTM.ComputableInO.decideEq'`, `.natIsZero'`: tests against a constant.
* `Turing.MultiTapeTM.ComputableInO.eq'`: equality of computed values, enabled locally by a client.
* `Turing.MultiTapeTM.ComputableInO.iteDecide`: case distinction on a decidable proposition.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

variable {α γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
  {T S T₁ S₁ T₂ S₂ T₃ S₃ : γ → ℕ}

/-- The linear primitive `h` as a `fun_prop` rule. -/
local macro "linear_rule " n:ident " : " f:term " from " e₁:term " to " e₂:term " := " h:term :
    command =>
  `(@[fun_prop] theorem $n : ComputableInO $f $e₁ $e₂
      (fun a => ($e₁ a).length) fun a => ($e₁ a).length := ComputableInDegree.inO_one $h)

linear_rule cons' : (fun p : α × List α => p.1 :: p.2) from (encPair enc (encList enc))
  to (encList enc) := ComputableInDegree.cons enc
linear_rule snoc' : (fun p : List α × α => p.1 ++ [p.2]) from (encPair (encList enc) enc)
  to (encList enc) := ComputableInDegree.snoc enc
linear_rule tail' : (fun l : List α => l.tail) from (encList enc) to (encList enc) :=
  ComputableInDegree.listTail enc

/-- Whether a computed list is empty. The list is a premise since a Boolean does not determine its
encoding. -/
@[fun_prop]
theorem isEmpty' {l : γ → List α} (hl : ComputableInO l encIn (encList enc) T₁ S₁) :
    ComputableInO (fun x => (l x).isEmpty) encIn encBool
      (fun x => T₁ x + (encList enc (l x)).length) fun x => S₁ x + (encList enc (l x)).length :=
  ComputableInO.comp' (ComputableInDegree.listIsEmpty enc).inO_one hl

@[fun_prop]
theorem headD' (d : α) : ComputableInO (fun l : List α => l.headD d) (encList enc) enc
    (fun l => (encList enc l).length) fun l => (encList enc l).length :=
  (ComputableInDegree.listHeadD enc d).inO_one

@[fun_prop]
theorem some' : ComputableInO (fun a : α => some a) enc (encOption enc)
    (fun a => (enc a).length) fun a => (enc a).length :=
  (ComputableInDegree.optionSome (enc₁ := enc) (enc := encOption enc)).inO_one

@[fun_prop]
theorem unarySucc' : ComputableInO (fun n : ℕ => n + 1) encUnary encUnary
    (fun n => (encUnary n).length) fun n => (encUnary n).length :=
  ComputableInDegree.unary_succ.inO_one

@[fun_prop]
theorem unaryPred' : ComputableInO (fun n : ℕ => n - 1) encUnary encUnary
    (fun n => (encUnary n).length) fun n => (encUnary n).length :=
  ComputableInDegree.unary_pred.inO_one

/-- The first `n x` elements of `l x`, with the count in unary. -/
@[fun_prop]
theorem take' {l : γ → List α} {n : γ → ℕ} (hl : ComputableInO l encIn (encList enc) T₁ S₁)
    (hn : ComputableInO n encIn encUnary T₂ S₂) :
    ComputableInO (fun x => (l x).take (n x)) encIn (encList enc)
      (fun x => T₁ x + T₂ x + (encPair (encList enc) encUnary (l x, n x)).length)
      fun x => S₁ x + S₂ x + (encPair (encList enc) encUnary (l x, n x)).length :=
  ComputableInO.comp' (f := fun p : List α × ℕ => p.1.take p.2)
    (ComputableInDegree.takeUnary enc).inO_one (hl.prod hn)

/-- All but the first `n x` elements of `l x`, with the count in unary. -/
@[fun_prop]
theorem drop' {l : γ → List α} {n : γ → ℕ} (hl : ComputableInO l encIn (encList enc) T₁ S₁)
    (hn : ComputableInO n encIn encUnary T₂ S₂) :
    ComputableInO (fun x => (l x).drop (n x)) encIn (encList enc)
      (fun x => T₁ x + T₂ x + (encPair (encList enc) encUnary (l x, n x)).length)
      fun x => S₁ x + S₂ x + (encPair (encList enc) encUnary (l x, n x)).length :=
  ComputableInO.comp' (f := fun p : List α × ℕ => p.1.drop p.2)
    (ComputableInDegree.dropUnary enc).inO_one (hl.prod hn)

attribute [fun_prop] natSucc natPred

/-- The negation of a computed Boolean. -/
@[fun_prop]
theorem not' {b : γ → Bool} (hb : ComputableInO b encIn encBool T S) :
    ComputableInO (fun x => !b x) encIn encBool T S :=
  (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool) not).inO_one.comp_linear hb

/-- The conjunction of two computed Booleans. -/
@[fun_prop]
theorem and' {a b : γ → Bool} (ha : ComputableInO a encIn encBool T₁ S₁)
    (hb : ComputableInO b encIn encBool T₂ S₂) :
    ComputableInO (fun x => a x && b x) encIn encBool (fun x => T₁ x + T₂ x)
      fun x => S₁ x + S₂ x :=
  (ComputableInDegree.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => q.1 && q.2).inO_one.comp_linear (ha.prod hb)

/-- The disjunction of two computed Booleans. -/
@[fun_prop]
theorem or' {a b : γ → Bool} (ha : ComputableInO a encIn encBool T₁ S₁)
    (hb : ComputableInO b encIn encBool T₂ S₂) :
    ComputableInO (fun x => a x || b x) encIn encBool (fun x => T₁ x + T₂ x)
      fun x => S₁ x + S₂ x :=
  (ComputableInDegree.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => q.1 || q.2).inO_one.comp_linear (ha.prod hb)

/-- Whether two computed values agree. This is not a global `fun_prop` rule, since it would also
apply to tests against a constant, which have cheaper rules; a client enables it locally. -/
theorem eq' [DecidableEq α] {a b : γ → α} (ha : ComputableInO a encIn enc T₁ S₁)
    (hb : ComputableInO b encIn enc T₂ S₂) :
    ComputableInO (fun x => decide (a x = b x)) encIn encBool
      (fun x => T₁ x + T₂ x +
        ((enc (a x)).length + 1) * ((enc (a x)).length + (enc (b x)).length + 1))
      fun x => S₁ x + S₂ x + (encPair enc enc (a x, b x)).length :=
  (eq enc).comp' (ha.prod hb)

/-- Whether a computed option is empty, within the bounds of the option. -/
@[fun_prop]
theorem optionIsNone {o : γ → Option α} (h : ComputableInO o encIn (encOption enc) T S) :
    ComputableInO (fun x => (o x).isNone) encIn encBool T S :=
  (not' h.optionIsSome).of_enc_eq fun x => by cases o x <;> rfl

/-- Convert an option to a zero- or one-element list in linear time and space, without assuming `α`
is inhabited. -/
theorem optionToList : ComputableInO (Option.toList (α := α)) (encOption enc) (encList enc)
    (fun o => (encOption enc o).length) fun o => (encOption enc o).length := by
  rcases isEmpty_or_nonempty α with h | h
  · exact (const (encIn := encOption enc) (encMid := encList enc) []).of_enc_eq fun o => by
      cases o with
      | none => rfl
      | some a => exact isEmptyElim a
  · obtain ⟨d⟩ := h
    have hsingle : ComputableInO (fun a : α => [a]) enc (encList enc)
        (fun a => (enc a).length) fun a => (enc a).length :=
      of_linear (.of_frame fun a => by rw [encList_cons, encList_nil, List.append_nil])
    refine (((optionIsSome id').ite (hsingle.comp_linear (optionGetD d id'))
      (const [])).of_enc_eq fun o => ?_).mono 2 (fun _ => ?_) fun _ => ?_
    · cases o <;> rfl
    all_goals split_ifs <;> omega

/-- Convert a computed option to a zero- or one-element list, within the bounds of the option. -/
@[fun_prop]
theorem optionToList' {o : γ → Option α} (h : ComputableInO o encIn (encOption enc) T S) :
    ComputableInO (fun x => (o x).toList) encIn (encList enc) T S :=
  optionToList.comp_linear h

/-- Concatenate two computed framed lists, adding their bounds. -/
@[fun_prop]
theorem listAppend' {u v : γ → List α} (hu : ComputableInO u encIn (encList enc) T₁ S₁)
    (hv : ComputableInO v encIn (encList enc) T₂ S₂) :
    ComputableInO (fun x => u x ++ v x) encIn (encList enc) (fun x => T₁ x + T₂ x)
      fun x => S₁ x + S₂ x :=
  (ComputableInDegree.listAppend enc).inO_one.comp_linear (hu.prod hv)

/-- Frame a computed bit string, within its bounds. -/
@[fun_prop]
theorem frame' {w : γ → List Bool} (hw : ComputableInO w encIn encBits T S) :
    ComputableInO (fun x => frame (w x)) encIn encBits T S :=
  (of_linear (ComputableInDegree.of_frame (encIn := encBits) (encMid := encBits)
    fun _ => rfl)).comp_linear hw

/-- Read the first framed word of a computed bit string, within its bounds. -/
@[fun_prop]
theorem unframe' {w : γ → List Bool} (hw : ComputableInO w encIn encBits T S) :
    ComputableInO (fun x => unframe (w x)) encIn encBits T S :=
  (of_linear (ComputableInDegree.of_unframe (encIn := encBits) (encMid := encBits)
    fun _ => rfl)).comp_linear hw

/-- Drop the first framed word of a computed bit string, within its bounds. -/
@[fun_prop]
theorem dropFrame' {w : γ → List Bool} (hw : ComputableInO w encIn encBits T S) :
    ComputableInO (fun x => dropFrame (w x)) encIn encBits T S :=
  (of_linear (ComputableInDegree.of_dropFrame (encIn := encBits) (encMid := encBits)
    fun _ => rfl)).comp_linear hw

/-- Concatenate two computed bit strings, adding their bounds. -/
@[fun_prop]
theorem bitsAppend' {u v : γ → List Bool} (hu : ComputableInO u encIn encBits T₁ S₁)
    (hv : ComputableInO v encIn encBits T₂ S₂) :
    ComputableInO (fun x => u x ++ v x) encIn encBits (fun x => T₁ x + T₂ x)
      fun x => S₁ x + S₂ x :=
  hu.append hv fun _ => rfl

/-- The unary length of a computed bit string, within its bounds. -/
@[fun_prop]
theorem bitsLengthUnary' {w : γ → List Bool} (hw : ComputableInO w encIn encBits T S) :
    ComputableInO (fun x => (w x).length) encIn encUnary T S :=
  lengthUnary.comp_linear hw

/-- Whether a computed value of a finite type equals a fixed value. -/
@[fun_prop]
theorem decideEq' [Finite α] [DecidableEq α] (c : α) {v : γ → α}
    (hv : ComputableInO v encIn enc T S) :
    ComputableInO (fun x => decide (v x = c)) encIn encBool T S :=
  (ComputableInDegree.of_finite (encIn := enc) (encMid := encBool)
    fun a => decide (a = c)).inO_one.comp_linear hv

/-- Whether a computed binary number is zero. -/
@[fun_prop]
theorem natIsZero' {n : γ → ℕ} (hn : ComputableInO n encIn encNat T S) :
    ComputableInO (fun x => decide (n x = 0)) encIn encBool T S :=
  natIsZero.comp_linear hn

/-- Case distinction on a decidable proposition, through its computed `decide`. -/
@[fun_prop]
theorem iteDecide {β : Type} {encOut : β ↪ List Bool} {c : γ → Prop} [DecidablePred c]
    {f g : γ → β} (hc : ComputableInO (fun x => decide (c x)) encIn encBool T₁ S₁)
    (hf : ComputableInO f encIn encOut T₂ S₂) (hg : ComputableInO g encIn encOut T₃ S₃) :
    ComputableInO (fun x => if c x then f x else g x) encIn encOut
      (fun x => T₁ x + if decide (c x) then T₂ x else T₃ x)
      fun x => S₁ x + if decide (c x) then S₂ x else S₃ x :=
  (hc.ite hf hg).of_enc_eq fun x => by simp only [decide_eq_true_eq]

-- Registered again so that a Boolean condition is tried here before `iteDecide`.
attribute [fun_prop] ite

end Turing.MultiTapeTM.ComputableInO

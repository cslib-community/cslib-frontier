/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-!
# Polynomial-time sum constructors and elimination

The two injections retain the supplied payload encoding and add its tag bit, reusing the linear time
and space certificates of `ComputableInO.inl` and `.inr`. Elimination branches via `Sum.getLeft?`,
`Sum.getRight?`, and `ComputableInPolyTime.optionElimWithInput`, retaining any captured input
without requiring `Inhabited`, `Finite`, or `Decoder` on either summand or on the result type.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.sumInl`, `.sumInr`: tagged sum construction.
* `Turing.MultiTapeTM.ComputableInPolyTime.sumGetLeft?`, `.sumGetRight?`: optional summand
  projection.
* `Turing.MultiTapeTM.ComputableInPolyTime.sumElim`: tagged sum elimination.
* `Turing.MultiTapeTM.ComputableInPolyTime.sumElimSnd`, `.sumElimWithInput`: tagged sum elimination
  retaining captured inputs.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type}

/-- Tag an encoded value as belonging to the left summand. -/
@[fun_prop]
theorem sumInl (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInPolyTime (Sum.inl (α := α) (β := β)) left (encSum left right) :=
  (ComputableInO.inl left right).computableInPolyTime .self .self

/-- Tag an encoded value as belonging to the right summand. -/
@[fun_prop]
theorem sumInr (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInPolyTime (Sum.inr (α := α) (β := β)) right (encSum left right) :=
  (ComputableInO.inr left right).computableInPolyTime .self .self

/-- Extract the optional left payload of a computed sum. -/
@[fun_prop]
theorem sumGetLeft? {γ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {eg : γ ↪ List Bool} {value : γ → α ⊕ β}
    (hv : ComputableInPolyTime value eg (encSum ea eb)) :
    ComputableInPolyTime (fun p => (value p).getLeft?) eg (encOption ea) :=
  (ComputableInO.getLeft?_deg ea eb).computableInPolyTime.comp hv

/-- Extract the optional right payload of a computed sum. -/
@[fun_prop]
theorem sumGetRight? {γ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {eg : γ ↪ List Bool} {value : γ → α ⊕ β}
    (hv : ComputableInPolyTime value eg (encSum ea eb)) :
    ComputableInPolyTime (fun p => (value p).getRight?) eg (encOption eb) :=
  (ComputableInO.getRight?_deg ea eb).computableInPolyTime.comp hv

/-- Eliminate the right component of a pair `γ × (α ⊕ β)` while retaining the captured input `γ`,
without requiring `Inhabited`, `Finite`, or `Decoder` on any type. -/
theorem sumElimSnd {γ δ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {eg : γ ↪ List Bool} {ed : δ ↪ List Bool}
    {left : γ → α → δ} {right : γ → β → δ}
    (hl : ComputableInPolyTime (fun p : γ × α => left p.1 p.2) (encPair eg ea) ed)
    (hr : ComputableInPolyTime (fun p : γ × β => right p.1 p.2) (encPair eg eb) ed) :
    ComputableInPolyTime
      (fun p : γ × (α ⊕ β) => p.2.elim (left p.1) (right p.1))
      (encPair eg (encSum ea eb)) ed := by
  rcases isEmpty_or_nonempty δ with hδ | ⟨⟨d⟩⟩
  · have : IsEmpty (γ × (α ⊕ β)) := ⟨fun ⟨g, s⟩ =>
      match s with
      | .inl a => isEmptyElim (left g a)
      | .inr b => isEmptyElim (right g b)⟩
    exact of_finite _
  · have hleft := sumGetLeft? (snd eg (encSum ea eb))
    have hright := sumGetRight? (snd eg (encSum ea eb))
    have hl' : ComputableInPolyTime (fun p : (γ × (α ⊕ β)) × α => left p.1.1 p.2)
        (encPair (encPair eg (encSum ea eb)) ea) ed :=
      hl.comp ((fst (encPair eg (encSum ea eb)) ea).fst'.prod (snd _ _))
    have hr' : ComputableInPolyTime (fun p : (γ × (α ⊕ β)) × β => right p.1.1 p.2)
        (encPair (encPair eg (encSum ea eb)) eb) ed :=
      hr.comp ((fst (encPair eg (encSum ea eb)) eb).fst'.prod (snd _ _))
    have h := hleft.optionElimWithInput (body := fun p a => left p.1 a)
      (hright.optionElimWithInput (body := fun p b => right p.1 b) (const d) hr') hl'
    refine h.of_enc_eq ?_
    rintro ⟨_, _ | _⟩ <;> rfl

/-- Eliminate a computed tagged sum while retaining the captured input `γ`, without requiring
`Inhabited`, `Finite`, or `Decoder` on any type. -/
@[fun_prop]
theorem sumElimWithInput {γ δ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {eg : γ ↪ List Bool} {ed : δ ↪ List Bool}
    {value : γ → α ⊕ β} {left : γ → α → δ} {right : γ → β → δ}
    (hv : ComputableInPolyTime value eg (encSum ea eb))
    (hl : ComputableInPolyTime (fun p : γ × α => left p.1 p.2) (encPair eg ea) ed)
    (hr : ComputableInPolyTime (fun p : γ × β => right p.1 p.2) (encPair eg eb) ed) :
    ComputableInPolyTime (fun p => (value p).elim (left p) (right p)) eg ed := by
  simpa only [Function.comp_def] using (sumElimSnd hl hr).comp (id'.prod hv)

/-- Eliminate a tagged sum in polynomial time on arbitrary summand and output encodings, without
requiring `Inhabited`, `Finite`, or `Decoder` on any type. -/
theorem sumElim {γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → γ} {g : β → γ}
    (hf : ComputableInPolyTime f encA encC) (hg : ComputableInPolyTime g encB encC) :
    ComputableInPolyTime (Sum.elim f g) (encSum encA encB) encC :=
  sumElimWithInput id' (hf.comp (snd (encSum encA encB) encA))
    (hg.comp (snd (encSum encA encB) encB))

end Turing.MultiTapeTM.ComputableInPolyTime

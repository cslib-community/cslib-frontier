/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Tactic.PolyTime.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Captured plain polynomial-time rules

Plain `Turing.MultiTapeTM.ComputableInPolyTime` composition rules for operations that combine
multiple arguments computed from a shared input. Rules whose head and encoding disambiguate
search are registered with `fun_prop`, and rules whose result hides an element or index encoding
additionally carry `program_certificate`; `binary_mod'` stays explicit alongside
`Turing.MultiTapeTM.ComputableInPolyTime.binary_div'` so `HMod.hMod` automation on
`Turing.MultiTapeTM.encUnary` remains unambiguous.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.bool_and'`,
  `Turing.MultiTapeTM.ComputableInPolyTime.bool_or'`: captured Boolean conjunction and disjunction
  registered for `fun_prop` and `polytime`.
* `Turing.MultiTapeTM.ComputableInPolyTime.cond'`: Boolean `_root_.cond` case distinction.
* `Turing.MultiTapeTM.ComputableInPolyTime.bitsHeadDWithInput`: head of a computed bit string with a
  computed Boolean fallback, fixing `encBits` and `encBool` without `ListEncoding` synthesis.
* `Turing.MultiTapeTM.ComputableInPolyTime.listHead?WithInput`: optional head of a computed
  framed list, fixing the element encoding without typeclass synthesis.
* `Turing.MultiTapeTM.ComputableInPolyTime.listSetWithInput`: replace a computed framed-list entry
  at a computed unary index.
* `Turing.MultiTapeTM.ComputableInPolyTime.listHeadDWithInput`: head of a computed framed list
  with a computed fallback.
* `Turing.MultiTapeTM.ComputableInPolyTime.listTakeWithInput`: prefix of a computed framed list
  of computed unary length.
* `Turing.MultiTapeTM.ComputableInPolyTime.listDropWithInput`: suffix of a computed framed list
  after dropping a computed unary prefix.
* `Turing.MultiTapeTM.ComputableInPolyTime.countWithInput`: unary occurrence count of a computed
  value in a computed framed list.
* `Turing.MultiTapeTM.ComputableInPolyTime.anyConst`: existential Boolean scan over a fixed list
  with input-dependent predicates.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_mod'`: explicit remainder of computed binary
  naturals on `Turing.MultiTapeTM.encNat`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

attribute [fun_prop] bool_and' bool_or'

/-- Case distinction on a computed Boolean guard in any encoding of `Bool`, for `_root_.cond`. -/
@[fun_prop]
public theorem cond' {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {encC : Bool ↪ List Bool} {c : α → Bool} {t e : α → β}
    (hc : ComputableInPolyTime c encIn encC) (ht : ComputableInPolyTime t encIn encOut)
    (he : ComputableInPolyTime e encIn encOut) :
    ComputableInPolyTime (fun a => _root_.cond (c a) (t a) (e a)) encIn encOut :=
  (hc.ite ht he).of_enc_eq fun a => by cases c a <;> rfl

/-- Read the head of a computed bit string with a computed Boolean fallback, fixing the word and
result encodings without waiting on `ListEncoding` synthesis. -/
@[fun_prop]
public theorem bitsHeadDWithInput {γ : Type} {encIn : γ ↪ List Bool}
    {word : γ → List Bool} {fallback : γ → Bool}
    (hword : ComputableInPolyTime word encIn encBits)
    (hfallback : ComputableInPolyTime fallback encIn encBool) :
    ComputableInPolyTime (fun a => (word a).headD (fallback a)) encIn encBool :=
  ((bitsIsEmpty.comp hword).ite hfallback ((headD false).comp hword)).of_enc_eq fun a => by
    simp only [Function.comp_apply]
    cases word a <;> rfl

/-- Read the optional head of a computed framed list, inferring the element encoding directly
from the list certificate without waiting on `ListEncoding` synthesis. -/
@[fun_prop, program_certificate hlist]
public theorem listHead?WithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun a => (list a).head?) encIn (encOption encA) :=
  (head? encA).comp hlist

/-- Replace a computed list entry at a unary index. Out-of-range indices preserve the list;
the replacement and both slices are charged in their original element encoding. -/
@[fun_prop]
public theorem listSetWithInput {γ α : Type} {encIn : γ ↪ List Bool} (encA : α ↪ List Bool)
    {list : γ → List α} {idx : γ → ℕ} {val : γ → α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hidx : ComputableInPolyTime idx encIn encUnary)
    (hval : ComputableInPolyTime val encIn encA) :
    ComputableInPolyTime (fun x => (list x).set (idx x) (val x)) encIn (encList encA) := by
  simp_rw [List.set_eq_take_append_cons_drop]
  exact ite_decide
    (unary_lt' hidx ((length_list encA).comp hlist))
    (listAppend'
      (listTakeWithInput hlist hidx)
      (cons' hval (listDropWithInput hlist (unary_add.comp (hidx.prod (const 1))))))
    hlist

end Turing.MultiTapeTM.ComputableInPolyTime

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import CslibFrontier.Computability.Encoding.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.WordPredicates
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum

-- vendored: canonical tagged options follow #1213; the kernel halt protocol stays explicit.

/-!
# The encoding of options

`encOption enc` encodes `none` as `[false]` and `some a` as `true` followed by `enc a`. It has
the capabilities of `Turing.MultiTapeTM.OptionEncoding`.

## Main definitions

* `Turing.MultiTapeTM.encOption`: the encoding of options.
-/

namespace Turing.MultiTapeTM

universe u

variable {α : Type u}

/-- Options encoded with `none` as `[false]` and `some a` as `true` followed by `enc a`. -/
public abbrev encOption (enc : α ↪ List Bool) : Option α ↪ List Bool :=
  Cslib.Encoding.encOption enc

variable {enc : α ↪ List Bool}

@[simp]
public lemma encOption_none : encOption enc none = [false] := rfl

@[simp]
public lemma encOption_some (a : α) : encOption enc (some a) = true :: enc a := rfl

/-- Internal iteration state: `none` is the kernel's empty-word halt signal, while `some`
prepends `true`. This is deliberately distinct from canonical tagged options. -/
@[expose] public def encHaltOption (enc : α ↪ List Bool) : Option α ↪ List Bool :=
  ⟨fun o => o.elim [] (true :: enc ·), by rintro (_ | a) (_ | b) h <;> simp_all⟩

@[simp] public theorem encHaltOption_none : encHaltOption enc none = [] := rfl
@[simp] public theorem encHaltOption_some (a : α) :
    encHaltOption enc (some a) = true :: enc a := rfl

public instance : HaltOptionEncoding enc (encHaltOption enc) where
  none_eq := rfl
  isSome := Internal.WordPredicates.computableInDegree_of_nonemptyT fun o => by
    cases o with
    | none => rfl
    | some a =>
      change [true] = [true] ++ Internal.WordPredicates.nonemptyT.run true (enc a)
      rw [Internal.WordPredicates.nonemptyT_run_true, List.append_nil]
  some := .of_cons_true fun _ => rfl
  getD d := .of_isEmpty_ite d (fun o ho => by cases o <;> simp_all)
    (.of_tail fun ⟨o, ho⟩ => by cases o <;> simp at ho ⊢)

/-- Protocol responses with no emitted bits on rejection. This is the same wire protocol as
`encHaltOption`, named for callers which concatenate responses rather than iterating. -/
public abbrev encSilentOption (enc : α ↪ List Bool) : Option α ↪ List Bool := encHaltOption enc

@[simp] public theorem encSilentOption_none : encSilentOption enc none = [] := rfl
@[simp] public theorem encSilentOption_some (a : α) :
    encSilentOption enc (some a) = true :: enc a := rfl

public instance : OptionEncoding enc (encOption enc) where
  isSome := by
    let e := (Equiv.optionEquivSumPUnit.{0} α).trans (Equiv.sumComm α Unit)
    exact ((ComputableInDegree.sumIsRight (Cslib.Encoding.encSubsingleton Unit) enc).of_encIn_eq
      e (fun _ => rfl)).of_enc_eq fun o => by cases o <;> rfl
  some := by
    exact (ComputableInDegree.inr (Cslib.Encoding.encSubsingleton Unit) enc).of_enc_eq
      fun _ => rfl
  getD d := by
    let e := (Equiv.optionEquivSumPUnit.{0} α).trans (Equiv.sumComm α Unit)
    exact ((ComputableInDegree.sumRightD (Cslib.Encoding.encSubsingleton Unit) enc d).of_encIn_eq
      e (fun _ => rfl)).of_enc_eq fun o => by cases o <;> rfl

end Turing.MultiTapeTM

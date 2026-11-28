/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Foundations.Data.List.Fold

/-!
# Finite case analysis within asymptotic bounds

A computed key of a fixed finite type selects one of finitely many branches, each of which
receives the original input. The dispatch chains `Turing.MultiTapeTM.ComputableInO.ite` over an
enumeration of the key type, testing the key against each value; since the enumeration is fixed,
its length only affects the hidden constant. Neither the key nor the result type needs an
inhabitant. The same chaining gives the disjunction of a fixed finite list of computed Booleans.

## Main results

* `Turing.MultiTapeTM.ComputableInO.finite_cases`: dispatch on a computed finite key, within the
  key's bounds plus a common branch bound.
* `Turing.MultiTapeTM.ComputableInO.list_any`: the disjunction of a fixed finite list of computed
  Booleans, within their common bound.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

variable {α β : Type} {encIn : α ↪ List Bool}

/-- A computed key of a fixed finite type selects a branch on the original input, within the key's
bounds plus a common bound for the branches. This also handles an empty key type (and hence an
empty input type). -/
theorem finite_cases {Tag : Type} [Finite Tag] {encOut : β ↪ List Bool}
    {tagEncoding : Tag ↪ List Bool} {key : α → Tag} {branch : Tag → α → β} {T₀ S₀ T S : α → ℕ}
    (hkey : ComputableInO key encIn tagEncoding T₀ S₀)
    (hbranch : ∀ tag, ComputableInO (branch tag) encIn encOut T S) :
    ComputableInO (fun a => branch (key a) a) encIn encOut (fun a => T₀ a + T a)
      (fun a => S₀ a + S a) := by
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    have : IsEmpty α := ⟨fun a => isEmptyElim (key a)⟩
    exact (ComputableInDegree.of_finite (encIn := encIn) (encMid := encOut)
      fun a => branch (key a) a).inO_one.mono 0 isEmptyElim isEmptyElim
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hselect (tags : List Tag) : ComputableInO (fun a =>
        tags.foldr (fun tag rest => if key a = tag then branch tag a else rest)
          (branch fallback a)) encIn encOut (fun a => T₀ a + T a) (fun a => S₀ a + S a) := by
      induction tags with
      | nil =>
        exact (hbranch fallback).mono_le (fun _ => Nat.le_add_left _ _)
          (fun _ => Nat.le_add_left _ _)
      | cons tag tags ih =>
        refine (((hkey.decideEq' tag).ite (hbranch tag) ih).of_enc_eq fun a => ?_).mono 2
          (fun a => ?_) fun a => ?_
        · simp only [List.foldr_cons, decide_eq_true_eq]
        all_goals split_ifs <;> omega
    simpa only [List.foldr_ite_eq_of_mem, Finset.mem_toList, Finset.mem_univ] using
      hselect (Finset.univ.toList : List Tag)

/-- The disjunction of a fixed finite list of computed Booleans, within their common bounds.
The time bound also charges the input length, which pays for the constant answer of the empty
list. -/
theorem list_any {ι : Type} (l : List ι) {p : ι → α → Bool} {T S : α → ℕ}
    (hp : ∀ i ∈ l, ComputableInO (p i) encIn encBool T S) :
    ComputableInO (fun a => l.any fun i => p i a) encIn encBool
      (fun a => T a + (encIn a).length) S := by
  induction l with
  | nil => exact (constZero false).mono 1 (fun a => by omega) fun a => by omega
  | cons i l ih =>
    refine (((hp i List.mem_cons_self).or'
      (ih fun j hj => hp j (List.mem_cons_of_mem i hj))).of_enc_eq fun a => ?_).mono 2
        (fun a => ?_) fun a => ?_
    · simp only [List.any_cons]
    all_goals omega

end Turing.MultiTapeTM.ComputableInO

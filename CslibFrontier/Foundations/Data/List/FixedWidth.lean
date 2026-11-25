/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Function.Defs
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.List.SelfDelimiting

/-!
# Concatenations of blocks of one length

A substitution that replaces every letter by a block of the same positive length is injective on
words as soon as it is injective on letters (`List.flatMap_injective_of_forall_length_eq`): the
blocks can be read back one after the other. It is the case of blocks of one length of
`List.flatMap_inj_of_length_eq` for self-delimiting codes, since the length of the concatenation
gives the number of blocks. `List.flatMap_singleton_injective` is the case of
blocks of length one, and `List.length_flatMap_of_forall_length_eq` gives the length of such a
concatenation. Two substitutions whose blocks have the same lengths on the letters of a word give
the same concatenation exactly when they agree on these letters
(`List.flatMap_eq_flatMap_iff_of_forall_length_eq`).
-/

public section

/-- A substitution by blocks of one positive length is injective on words when it is injective on
letters. -/
theorem List.flatMap_injective_of_forall_length_eq {α β : Type*} {f : α → List β} {k : ℕ}
    (hk : 0 < k) (hlen : ∀ a, (f a).length = k) (hf : Function.Injective f) :
    Function.Injective fun w : List α => w.flatMap f := by
  intro w w' h
  refine List.flatMap_inj_of_length_eq (fun a a' r r' e => ?_) ?_ h
  · obtain ⟨h1, h2⟩ := List.append_inj e ((hlen a).trans (hlen a').symm)
    exact ⟨hf h1, h2⟩
  · have hl := congrArg List.length h
    rw [List.length_flatMap_of_forall_length_eq fun a _ => hlen a,
      List.length_flatMap_of_forall_length_eq fun a _ => hlen a] at hl
    exact Nat.eq_of_mul_eq_mul_right hk hl

/-- Two substitutions whose blocks have the same lengths on the letters of a word give the same
word exactly when they agree on its letters. -/
theorem List.flatMap_eq_flatMap_iff_of_forall_length_eq {α β : Type*} {l : List α}
    {f g : α → List β} (h : ∀ a ∈ l, (f a).length = (g a).length) :
    l.flatMap f = l.flatMap g ↔ ∀ a ∈ l, f a = g a := by
  refine ⟨fun e => ?_, List.flatMap_congr⟩
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons] at e
    obtain ⟨e1, e2⟩ := List.append_inj e (h a List.mem_cons_self)
    exact List.forall_mem_cons.2 ⟨e1, ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) e2⟩

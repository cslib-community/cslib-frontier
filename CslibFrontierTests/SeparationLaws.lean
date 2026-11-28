/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Contract
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Law
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Fintype.BigOperators

/-! Tests of laws and of the contraction of code words, as a client that sees only the public
statements.

* The *equality law*: two roles share one slot and one channel, and the two copies of the bit of
  the slot agree exactly when both are the bit on the channel. This shows that `Cut.Law` is
  inhabited, and `Cut.Law.pow` gives the same identity for `B` bits.
* `Cut.sum_prod_codeTable` for two roles joined by one channel that carries one bit, which is its
  own code word.
* The entries of the equality law over `ℚ` are among `0` and `1`, finitely many; so its tables lie
  in the smallest subring of `ℚ`, and restricted to that subring it is a law with the same tables.
* The equality law over `ℤ`, mapped to `ℚ`, has the tables of the equality law over `ℚ`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationLaws

open Finset Cslib Cslib.Circuits.Arithmetic.Separation Cslib.Circuits.Arithmetic.Separation.Cut

variable {F : Type} [CommSemiring F]

/-- The equality law: the roles are `false` and `true`, with one slot and one channel between
them. There is one index, and the string on the channel is one bit. The table of a role is `1`
when its copy of the bit of the slot is the bit on the channel. -/
private def equalityLaw (F : Type) [CommSemiring F] : Law F where
  Role := Bool
  Slot := Unit
  Channel := Unit
  Index := Unit
  slotEnd _ d := d
  slotEnd_ne _ := by decide
  channelEnd _ d := d
  channelEnd_ne _ := by decide
  labelLength := 0
  label _ := Fin.elim0
  label_injective _ _ _ := rfl
  length _ _ := 1
  table p _ x g := if x ⟨(), p, rfl⟩ = g ⟨(), p, rfl⟩ 0 then 1 else 0
  identity X := by
    rw [Fintype.sum_unique, ← ((Equiv.funUnique Unit (BitString 1)).trans
      (Equiv.funUnique (Fin 1) Bool)).symm.sum_comp, Fintype.sum_bool]
    have hg (b : Bool) : ((Equiv.funUnique Unit (BitString 1)).trans
        (Equiv.funUnique (Fin 1) Bool)).symm b () 0 = b := rfl
    simp only [Fintype.prod_bool, hg]
    rcases Bool.eq_false_or_eq_true (X false ()) with hf | hf <;>
      rcases Bool.eq_false_or_eq_true (X true ()) with ht | ht <;> simp [hf, ht]
  connected _ _ _ _ := rfl

/-- The power of the equality law: `B` bits on the slot agree exactly when they are the `B` bits
chosen on the channel. -/
example (B : ℕ) (X : Bool → Fin B → Unit → Bool) :
    (if ∀ e k, X false k e = X true k e then (1 : F) else 0) =
      ∑ i : Fin B → Unit, ∑ g : Unit → (k : Fin B) → BitString 1,
        ∏ p, ∏ k, (equalityLaw F).table p (i k) (fun e => X p k e.val) fun ν => g ν.val k :=
  (equalityLaw F).pow B X

/-- The strings of the equality law have length at most one. -/
example : (equalityLaw F).LengthLE 1 := fun _ _ => le_rfl

/-- Two roles joined by one channel that carries a bit: summing the product of the two tables
with code words over the code word on the channel gives the sum of the products of the tables. -/
example (G : (p : Bool) → Unit → (({ν : Unit // Play.Holds (fun _ d => d) p ν}) → Bool) → F) :
    ∑ z : Unit → Bool, ∏ p, codeTable (fun _ d => d) (fun _ _ b => b) p (G p) z =
      ∑ i : Unit, ∑ g : Unit → Bool, ∏ p, G p i fun ν => g ν :=
  sum_prod_codeTable (S := fun _ _ => Bool) (fun _ => by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    exact congrArg _ h) (fun _ _ _ _ => rfl) G

/-- The entries of the equality law over `ℚ` are among `0` and `1`, and there are finitely many. -/
private theorem entries_equalityLaw :
    (equalityLaw ℚ).entries ⊆ {0, 1} ∧ (equalityLaw ℚ).entries.Finite :=
  ⟨Set.iUnion_subset fun _ => Set.iUnion_subset fun _ => Set.iUnion_subset fun _ =>
    Set.range_subset_iff.2 fun _ => by simp only [equalityLaw]; split_ifs <;> simp,
    Law.finite_entries _⟩

/-- The tables of the equality law over `ℚ` lie in the smallest subring `⊥` of `ℚ`. -/
private theorem table_mem_bot (p : Bool) (i : Unit) (X g) :
    (equalityLaw ℚ).table p i X g ∈ (⊥ : Subring ℚ) := by
  rcases entries_equalityLaw.1 (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2
    ⟨X, Set.mem_range_self g⟩⟩⟩) with h | h <;> rw [h]
  exacts [zero_mem _, one_mem _]

/-- The equality law restricted to the smallest subring of `ℚ`: a law over that subring, with the
same tables. -/
example (p : Bool) (X g) :
    (((equalityLaw ℚ).restrict (⊥ : Subring ℚ) table_mem_bot).table p () X g : ℚ) =
      (equalityLaw ℚ).table p () X g :=
  rfl

/-- The restriction is a law over the subring with its own ring structure. -/
example : Law (⊥ : Subring ℚ) := (equalityLaw ℚ).restrict ⊥ table_mem_bot

/-- The equality law over `ℤ`, mapped to `ℚ`: a law over `ℚ` with the tables of the equality law
over `ℚ`. -/
example (p : Bool) (X g) :
    ((equalityLaw ℤ).map (Int.castRingHom ℚ)).table p () X g = (equalityLaw ℚ).table p () X g := by
  simp only [Law.map, equalityLaw]
  split_ifs <;> simp

end CslibFrontierTests.SeparationLaws

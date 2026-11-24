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
import Mathlib.Data.Fintype.BigOperators

/-! Tests of laws and of the contraction of code words, as a client that sees only the public
statements.

* The *equality law*: two roles share one slot and one channel, and the two copies of the bit of
  the slot agree exactly when both are the bit on the channel. This shows that `Cut.Law` is
  inhabited, and `Cut.Law.pow` gives the same identity for `B` bits.
* `Cut.sum_prod_codeTable` for two roles joined by one channel that carries one bit, which is its
  own code word. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationLaws

open Finset Cslib Cslib.Circuits.Arithmetic.Separation Cslib.Circuits.Arithmetic.Separation.Cut

variable {F : Type} [CommSemiring F]

/-- The equality law: the roles are `false` and `true`, with one slot and one channel between
them. There is one index, and the string on the channel is one bit. The table of a role is `1`
when its copy of the bit of the slot is the bit on the channel. -/
def equalityLaw (F : Type) [CommSemiring F] : Law F where
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
        ∏ p, ∏ k, (equalityLaw F).table p (i k) (fun e => X p k e.1) fun ν => g ν.1 k :=
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

end CslibFrontierTests.SeparationLaws

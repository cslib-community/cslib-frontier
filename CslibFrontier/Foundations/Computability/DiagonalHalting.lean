/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/PartrecCode.lean`)

public import CslibFrontier.Init
public import Mathlib.Computability.PartrecCode

/-!
# Ordinary diagonal halting

The diagonal halting set asks whether an ordinary partial recursive code halts on its own index.
A fixed partial recursive function's domain reduces to this set by specializing the program to
its input. The namespace is shared with the Kleene–Post construction that uses the halting set.

## Main results

* `exists_primrec_reduce_dom_to_halting`: the domain of a partial recursive function is a
  primitive recursive preimage of the diagonal halting set.
-/

public section

open Encodable Denumerable

namespace Nat.RecursiveIn.KleenePost

/-- The Turing jump of the empty set, the diagonal halting set for partial recursive functions. -/
@[expose]
def halting : Set ℕ := { c | (Nat.Partrec.Code.eval (ofNat Nat.Partrec.Code c) c).Dom }

/-- Halting of a partial recursive function is a primitive recursive preimage of the
ordinary diagonal halting set. -/
lemma exists_primrec_reduce_dom_to_halting {α : Type*} [Primcodable α] {f : α →. ℕ}
    (hf : Partrec f) :
    ∃ K : α → ℕ, _root_.Primrec K ∧ ∀ a, (f a).Dom ↔ K a ∈ halting := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  let K := fun a : α =>
    encode (Nat.Partrec.Code.comp c (Nat.Partrec.Code.const (encode a)))
  refine ⟨K, _root_.Primrec.encode.comp
    (Nat.Partrec.Code.primrec₂_comp.comp (_root_.Primrec.const c)
      (Nat.Partrec.Code.primrec_const.comp _root_.Primrec.encode)), fun a => ?_⟩
  change _ ↔ (Nat.Partrec.Code.eval (ofNat Nat.Partrec.Code (K a)) (K a)).Dom
  change _ ↔ (Nat.Partrec.Code.eval (ofNat Nat.Partrec.Code (encode _)) (K a)).Dom
  rw [ofNat_encode]
  change _ ↔ (((Nat.Partrec.Code.const (encode a)).eval (K a)).bind
    (fun m => c.eval m)).Dom
  rw [Nat.Partrec.Code.eval_const, Part.bind_some, hc]
  simp [encodek]

end Nat.RecursiveIn.KleenePost

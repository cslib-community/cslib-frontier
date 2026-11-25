/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Tactic.PolyTime

/-!
# Ordinary-import checks for `PolyTime.Sum`

Tagged encodings, empty summands, constructor certificates, `sumGetLeft?` / `sumGetRight?`,
point-free `Sum.elim`, nested captured `sumElimWithInput`, and summand-encoding mismatch rejection.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PolyTimeSum

open Turing.MultiTapeTM

-- Equal empty payloads remain distinct because the tag is always present.
private def emptyUnit : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩

-- Equal empty payloads remain distinct because the tag is always present, and constructor
-- certificates capture payloads without requiring the other summand to be inhabited.
example {α β Input : Type} (left : α ↪ List Bool) (right : β ↪ List Bool)
    (input : Input ↪ List Bool) (f : Input → α) (g : Input → β)
    (hf : ComputableInPolyTime f input left) (hg : ComputableInPolyTime g input right)
    (empty : Empty ↪ List Bool) :
    encSum emptyUnit emptyUnit (.inl ()) = [false] ∧
    encSum emptyUnit emptyUnit (.inr ()) = [true] ∧
    (encSum encUnary encBits (.inr [false, true])).length = 3 ∧
    ComputableInPolyTime (fun x => Sum.inl (f x)) input (encSum left right) ∧
    ComputableInPolyTime (fun x => let value := g x; Sum.inr value) input (encSum left right) ∧
    ComputableInPolyTime (Sum.inr : ℕ → Empty ⊕ ℕ) encUnary (encSum empty encUnary) ∧
    ComputableInPolyTime (Sum.inl : ℕ → ℕ ⊕ Empty) encUnary (encSum encUnary empty) := by
  refine ⟨rfl, rfl, rfl, ?_, by fun_prop, by fun_prop, by fun_prop⟩
  fail_if_success (clear hf; fun_prop)
  fun_prop

example : ComputableInPolyTime
    (fun s : ℕ ⊕ (ℕ × Bool) => (s.getLeft?, s.getRight?))
    (encSum encNat (encPair encUnary encBool))
    (encPair (encOption encNat) (encOption (encPair encUnary encBool))) := by
  fun_prop

example : ComputableInPolyTime
    (Sum.elim (fun n : ℕ => n + 1) (fun b : Bool => if b then 2 else 0))
    (encSum encNat encBool) encNat := by
  fun_prop

example : ComputableInPolyTime
    (fun p : ℕ × (ℕ ⊕ (Bool ⊕ ℕ)) =>
      p.2.elim (fun n => p.1 + n)
        (fun rest => rest.elim (fun b => if b then p.1 else 0) (fun m => p.1 * m)))
    (encPair encNat (encSum encNat (encSum encBool encNat))) encNat := by
  fun_prop

-- Negative guard: `sumElimWithInput` must not conflate `encNat` and `encUnary` summand encodings.
example (f : ℕ → ℕ) (_hf : ComputableInPolyTime f encUnary encNat) : True := by
  fail_if_success
    exact (by fun_prop : ComputableInPolyTime (Sum.elim f id) (encSum encNat encNat) encNat)
  trivial

end CslibFrontierTests.PolyTimeSum

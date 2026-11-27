/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.CollisionResistant.GenericAttacks
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for brute force and the birthday attack as collision finders

Checks for `CslibFrontier/Crypto/Computational/CollisionResistant/GenericAttacks.lean` as a
`module` client with ordinary imports:

* Hypotheses that cannot be dropped: repeated messages (`hnd`), exactly `2 ^ ℓ` messages (`hlt`)
  and digests of other lengths (the brute-force `hlen`) give no collision; the identity hash has
  none at all (the birthday `hlen` and `hM`); a domain predicate that rejects every message
  (`hvalid`) leaves no collision; and `ℓ n = n` fails `hN`.
* `collidingPairList?` skips a repeated message and returns the next pair with equal digests.
* The book's example: 16-bit digests are not collision resistant, by brute force and by the
  birthday attack on 23-bit messages, whose count is the book's `⌈2 √(2 ^ 16)⌉ + 1 = 513`.
* Logarithmic digests `ℓ n = Nat.clog 2 n` satisfy `hN`, and both refutations apply to them.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CollisionResistantGenericAttacks

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-! ### Hypotheses that cannot be dropped -/

/-- `hnd`: three copies of one message under a constant 1-bit hash are not a collision, although
`3 > 2 ^ 1`. -/
example : collidingPairList? (fun _ : List Bool => [false]) [[], [], []] = none := by
  decide

/-- The first pair with equal digests is the repeated message `[]`. Steps 4 and 5 of Algorithm
BirthdayAttack would stop there and fail; the search skips it and returns the next pair. -/
example :
    collidingPairList? (fun _ : List Bool => [false]) [[], [], [true]] = some ([], [true]) := by
  decide

/-- `hlt` is strict: `2 ^ ℓ` distinct messages need not collide (`ℓ = 1`). -/
example : collidingPairList? (fun m : List Bool => m) [[false], [true]] = none := by
  decide

/-- The brute-force `hlen`: with digests of other lengths, `3 > 2 ^ 1` distinct messages need not
collide (the identity hash). -/
example : collidingPairList? (fun m : List Bool => m) [[], [false], [true]] = none := by
  decide

/-- The birthday `hlen` and `hM`: the identity hash has no collision at all. It satisfies `hlen`
with `ℓ = msgLen` (then `hM` fails) and `hM` with `msgLen = ℓ + 7` (then `hlen` fails). -/
example (valid : ℕ → List Bool → Bool) (n : ℕ) (k a b : List Bool) :
    isCollision (fun _ m => m) valid n k a b = false := by
  by_cases h : a = b <;> simp [isCollision, h]

/-- `hvalid`: if `valid` rejects the messages, nothing is a collision. -/
example (H : List Bool → List Bool → List Bool) (n : ℕ) (k a b : List Bool) :
    isCollision H (fun _ _ => false) n k a b = false := by
  simp [isCollision]

/-- `hN`: digests as long as the security parameter, `ℓ n = n`, fail it. -/
example : ¬ ComputableInPolyTime (fun n : ℕ => 2 ^ n) encUnary encUnary := by
  intro h
  have hb : PolyBounded (fun n : ℕ => n) (fun n : ℕ => 2 ^ n) := by
    simpa [encUnary_apply] using h.polyBounded
  obtain ⟨n, hn⟩ := (Cslib.PolynomiallyBounded.eventually_lt_two_pow
    (PolyBounded.polynomiallyBounded (f := fun n => 2 ^ n) hb)).exists
  exact lt_irrefl _ hn

/-! ### The book's 16-bit example -/

/-- 16-bit digests are not collision resistant, by brute force. -/
example {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = 16) : ¬ CollisionResistant H :=
  not_collisionResistant_of_two_pow_polyTime (ℓ := fun _ => 16) hH (.const _) hlen

/-- The same by the birthday attack, with 23-bit messages (`2 ^ 23 ≥ 100 · 2 ^ 16`). -/
example {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = 16) : ¬ CollisionResistant H :=
  not_collisionResistantOn_of_birthday (ℓ := fun _ => 16) (msgLen := fun _ => 23) hH
    (.const _) (.const _) (fun k m _ => hlen k m) (fun _ _ _ => rfl) (fun _ => by norm_num)

/-- The birthday finder then samples `⌈2 √(2 ^ 16)⌉ + 1 = 513` messages. -/
example : ⌈2 * Real.sqrt ((2 ^ 16 : ℕ) : ℝ)⌉₊ + 1 = 513 := by
  rw [show ((2 ^ 16 : ℕ) : ℝ) = 256 ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
    show (2 : ℝ) * 256 = ((512 : ℕ) : ℝ) by norm_num, Nat.ceil_natCast]

/-! ### Logarithmic digest length -/

/-- `ℓ n = Nat.clog 2 n` satisfies `hN`. -/
example : ComputableInPolyTime (fun n : ℕ => 2 ^ Nat.clog 2 n) encUnary encUnary := by
  fun_prop

/-- Digests of `⌈log₂ n⌉` bits are not collision resistant, by brute force. -/
example {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = Nat.clog 2 k.length) : ¬ CollisionResistant H :=
  not_collisionResistant_of_two_pow_polyTime (ℓ := fun n => Nat.clog 2 n) hH (by fun_prop) hlen

/-- The same by the birthday attack, with messages 7 bits longer than the digests. -/
example {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = Nat.clog 2 k.length) : ¬ CollisionResistant H :=
  not_collisionResistantOn_of_birthday (ℓ := fun n => Nat.clog 2 n)
    (msgLen := fun n => Nat.clog 2 n + 7) hH (by fun_prop) (by fun_prop)
    (fun k m _ => hlen k m) (fun _ _ _ => rfl) (fun n => by rw [pow_add]; omega)

end CslibFrontierTests.CollisionResistantGenericAttacks

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.TargetCollisionResistant
import CslibFrontier.Tactic.PolyTime

/-! Shared constant `KeyedHashFamily` fixture (`0^{n+1}`) for cryptography test suites. -/

public section

namespace CslibFrontierTests.Crypto

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- Constant `KeyedHashFamily` with `keyLen n = n` and `digestLen n = n + 1` mapping every input
to `0^{n+1}`. -/
@[expose] def zeroKeyedHashFamily : KeyedHashFamily where
  keyLen n := n
  digestLen n := n + 1
  eval n _ _ := List.replicate (n + 1) false
  keyLen_polyTime := .id'
  digestLen_polyTime := by polytime
  le_digestLen _ := Nat.le_succ _
  polyTime := by polytime
  length_eq _ _ _ _ := List.length_replicate

@[simp] theorem zeroKeyedHashFamily_keyLen (n : ℕ) : zeroKeyedHashFamily.keyLen n = n := rfl

@[simp] theorem zeroKeyedHashFamily_digestLen (n : ℕ) :
    zeroKeyedHashFamily.digestLen n = n + 1 := rfl

@[simp] theorem zeroKeyedHashFamily_eval (n : ℕ) (k msg : List Bool) :
    zeroKeyedHashFamily.eval n k msg = List.replicate (n + 1) false := rfl

end CslibFrontierTests.Crypto

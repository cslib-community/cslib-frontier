/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Tactic.PolyTime

/-!
# Flipping the leading bit of a bit string

Shared bit-string helper `Cslib.Crypto.flipHeadBit`, used across second-preimage resistance
separations (`CslibFrontier/Crypto/Computational/SecondPreimageResistant/Relations.lean`)
and unauthenticated-IV counterexamples
(`CslibFrontier/Crypto/Computational/Encryption/EncryptThenMAC/PartialTag.lean`).

## Main definitions

* `Cslib.Crypto.flipHeadBit`: flip the first bit of a word, mapping `[]` to `[true]`.

## Main results

* `Cslib.Crypto.flipHeadBit_ne_self`: flipping the leading bit always produces a distinct word.
* `Cslib.Crypto.computableInPolyTime_flipHeadBit`: polynomial-time certificate for `flipHeadBit`.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- Flip the first bit of a word (mapping `[]` to `[true]`), producing a distinct word with the
same tail. -/
@[expose]
def flipHeadBit (w : List Bool) : List Bool :=
  (!w.headD false) :: w.tail

theorem flipHeadBit_ne_self (w : List Bool) : flipHeadBit w ≠ w := by
  intro h
  have hhead := congrArg (fun l => l.headD false) h
  simp [flipHeadBit] at hhead

@[fun_prop]
theorem computableInPolyTime_flipHeadBit :
    ComputableInPolyTime flipHeadBit encBits encBits := by
  exact ComputableInPolyTime.bitsCons
    (ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false))
    ComputableInPolyTime.bitsTail

end Cslib.Crypto

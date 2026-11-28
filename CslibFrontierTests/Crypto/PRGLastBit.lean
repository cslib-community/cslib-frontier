/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.Stretch.Prefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Goldreich's Construction 8.7 and Proposition 8.8: the emitted last bits of a one-bit
generator, evaluated on a toy rotation generator, and the theorem applied at the quadratic stretch
`ℓ(n) = n * n + 1`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.PRGLastBit

open Cslib.Crypto Cslib.Crypto.PRGStretch Turing.MultiTapeTM

/-- A toy one-bit expansion: rotate the seed left by one bit and append the bit rotated out. The
next seed `xᵢ₊₁` is the rotation and the emitted bit `σᵢ₊₁` is the first bit of `xᵢ`. -/
def rotate (s : List Bool) : List Bool := s.drop 1 ++ s.take 1 ++ [s.headD false]

theorem length_rotate (s : List Bool) : (rotate s).length = s.length + 1 := by
  cases s <;> simp [rotate]

/-- Construction 8.7 on the rotation emits the seed cyclically: `σ₁ ⋯ σ₅` from `100`. -/
example : (forwardIterate rotate 5 [true, false, false]).take 5 =
    [true, false, false, true, false] := by
  decide

/-- The same output computed from the draft's recurrence `xᵢσᵢ = G₁(xᵢ₋₁)`. -/
example :
    ((List.range 5).map fun i => emitBit rotate (seedAt rotate [true, false, false] i)).flatten =
      [true, false, false, true, false] := by
  rw [← take_forwardIterate_eq_flatten_emitBit length_rotate]
  decide

/-- Proposition 8.8 at the quadratic stretch `ℓ(n) = n * n + 1`, for any one-bit PRG. -/
example {generator : List Bool → List Bool}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1)) :
    PseudorandomGenerator
      (fun seed => (forwardIterate generator (seed.length * seed.length + 1) seed).take
        (seed.length * seed.length + 1))
      (fun n => n * n + 1) :=
  pseudorandomGenerator_take_forwardIterate hgenerator (ℓ := fun n => n * n + 1) (by fun_prop)
    fun n => by nlinarith

end CslibFrontierTests.PRGLastBit

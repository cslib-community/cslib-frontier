/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient

/-!
# Tests for efficient point-and-permute garbling

A client of `CslibFrontier.Crypto.Primitives.Garbling.Efficient` and
`CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient` under module encapsulation.

`Scheme.encGarbled`, declared with `enc_structure`, writes the same words as the former tuple
encoding `encPair encBits (encPair encBits encBits)` of `(F, e, d)`. `Scheme.IsEfficient` has an
instance: point-and-permute garbling keyed by the family that returns its input word, which is
computed in polynomial time.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GarblingPointPermute

open Cslib.Crypto.Garbling Turing.MultiTapeTM

/-- The encoded words of a garbled triple are unchanged by the `enc_structure` declaration. -/
example (g : Scheme.Garbled) :
    Scheme.encGarbled g = encPair encBits (encPair encBits encBits) (g.fn, g.encInfo, g.decInfo) :=
  rfl

/-- Point-and-permute garbling keyed by a polynomial-time family is efficient. -/
example : (PointPermute.scheme fun _ x => x).IsEfficient encValidCircuit :=
  PointPermute.scheme_isEfficient (ComputableInPolyTime.snd _ _)

end CslibFrontierTests.Crypto.GarblingPointPermute

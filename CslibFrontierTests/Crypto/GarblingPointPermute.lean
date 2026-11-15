/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Simulator
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Privacy

/-!
# Tests for efficient point-and-permute garbling

A client of `CslibFrontier.Crypto.Primitives.Garbling.Efficient` and
`CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient` under module encapsulation.

`Scheme.encGarbled`, declared with `enc_structure`, writes the same words as the former tuple
encoding `encPair encBits (encPair encBits encBits)` of `(F, e, d)`. `Scheme.IsEfficient` has an
instance: point-and-permute garbling keyed by the family that returns its input word, which is
computed in polynomial time. For the same family, the simulator `PointPermute.simWord` of
`CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Simulator` is PPT, and its views decode to
the output, and a pseudorandom family makes the scheme `prv.sim` secure.
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

/-- The simulator of point-and-permute garbling keyed by a polynomial-time family is PPT. -/
example : Cslib.Probability.IsPPTOn (encPair encUnary (encPair encBits encValidTopo)) encPrvView
    (fun (k, y, t) => PointPermute.simWord (fun _ x => x) k y t) :=
  PointPermute.isPPTOn_simWord (ComputableInPolyTime.snd _ _)

/-- Every simulated view decodes to the output. -/
example (k : ℕ) (t : ValidTopo) (y coins : List Bool) (hy : y.length = t.1.m) :
    let V := PointPermute.simViewWord (fun _ x => x) k y t.1 coins
    PointPermute.decodeWord V.decInfo (PointPermute.evalWord (fun _ x => x) V.fn V.input) =
      some y :=
  PointPermute.decodeWord_evalWord_simViewWord _ k t hy coins

/-- A client applies the privacy theorem through the module interface. -/
example {family : List Bool → List Bool → List Bool}
    (h : Cslib.Crypto.PseudorandomFunction family) :
    (PointPermute.scheme family).PrvSimSecure phiTopo encValidCircuit encValidTopo :=
  h.prvSim_pointPermute

end CslibFrontierTests.Crypto.GarblingPointPermute

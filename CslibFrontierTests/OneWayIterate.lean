/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.OneWay.Iterate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Clients of the iterated one-way permutation theorem (Arora–Barak draft, Chapter 10,
Exercise 3): natural, fractional and constant iteration counts. -/

set_option linter.privateModule false

namespace CslibFrontierTests.OneWayIterate

open Cslib Cslib.Crypto Probability Turing.MultiTapeTM

variable {f : List Bool → List Bool}

/-- Natural exponents `c ≥ 0`, through the general count theorem. -/
example (hf : OneWayPermutation f) (c : ℕ) : OneWayPermutation (fun x => f^[x.length ^ c] x) :=
  hf.iterateByLength (k := fun n => n ^ c)
    (ComputableTidilyInPolyTime.unary_pow c).computableInPolyTime
    (Filter.eventually_atTop.2 ⟨1, fun n hn => pow_ne_zero c (by omega)⟩)

/-- The fractional exponent `c = 1 / 2`: iterate `⌈√|x|⌉` times. -/
example (hf : OneWayPermutation f) :
    OneWayPermutation (fun x => f^[⌈(x.length : ℝ) ^ ((1 : ℕ) / (2 : ℕ) : ℝ)⌉₊] x) :=
  hf.iterate_ceil_rpow 1 2 two_ne_zero

/-- A constant count `3` is also covered. -/
example (hf : OneWayPermutation f) : OneWayPermutation (fun x => f^[3] x) :=
  hf.iterateByLength (k := fun _ => 3) (ComputableInPolyTime.const 3)
    (Filter.Eventually.of_forall fun _ => three_ne_zero)

/-- At a length where the count is positive, the derived inverter for `f` succeeds exactly as
often as the given inverter for the iterate. -/
example (hf : OneWayPermutation f) (adversary : Inverter) (n : ℕ) :
    ProbComp.eval (inversionGame (iterateByLength f fun m => m + 1) adversary n) =
      ProbComp.eval
        (inversionGame f (iterateInverter f (fun m => m + 1) adversary) n) :=
  eval_inversionGame_iterateByLength hf.length_eq hf.bijective adversary n.succ_ne_zero

end CslibFrontierTests.OneWayIterate

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Crypto.Computational.HardCore.NoUniversal

/-! Checked clients of the impossibility of a universal hard-core predicate
(Goldreich, Exercise 7.8). -/

set_option linter.privateModule false

namespace CslibFrontierTests.HardCoreNoUniversal

open Cslib Cslib.Crypto Turing.MultiTapeTM

-- The appended bit is the last bit of the image.
example (f : List Bool → List Bool) (b : List Bool → Bool) (x : List Bool) :
    (appendPredicate f b x).getLastD false = b x := by
  simp only [appendPredicate, List.getLastD_concat]

-- Appending a polynomial-time bit to a one-way function keeps it one-way.
example {f : List Bool → List Bool} (hf : OneWay f) :
    OneWay (appendPredicate f (List.getLastD · false)) :=
  hf.appendPredicate computableInPolyTime_getLastD

-- No predicate, efficient or not, is a hard-core of its own appended function.
example (b : List Bool → Bool) : ¬ HardCore (appendPredicate (fun x => x) b) b :=
  not_hardCore_appendPredicate _ b

-- Even an empty image acquires the fixed bit, which the predictor reads without a length.
example : lastBitPredictor 0 (appendPredicate id (fun _ => true) []) = pure true :=
  rfl

end CslibFrontierTests.HardCoreNoUniversal
